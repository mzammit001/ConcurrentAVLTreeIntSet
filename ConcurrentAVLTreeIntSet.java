import java.io.Closeable;
import java.util.*;
import java.lang.Math.*;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.locks.*;
import java.util.concurrent.locks.StampedLock;

/*
 * AVL Tree using iterative insert/remove
 * and storing heights in nodes
 *
 * re-balancing based on
 * https://www.geeksforgeeks.org/avl-tree-set-1-insertion/
 * https://www.geeksforgeeks.org/avl-tree-set-2-deletion/
 *
 */
public class ConcurrentAVLTreeIntSet implements Closeable  {
    protected Node root;
    protected StampedLock balanceMutex;
    protected int updates;
    protected AtomicBoolean condition;
    protected boolean destroy;
    protected int balanceThresh = 500;
    private Runnable balanceRunnable;
    private Thread balanceThread;

    public ConcurrentAVLTreeIntSet() {
        root = new Node();
        balanceMutex = new StampedLock();
        updates = 0;
        destroy = false;
        // condition to wake periodic thread from sleep
        condition = new AtomicBoolean(false);
        // start the background rebalancing thread
        startPeriodicThread(this);
    }

    private void startPeriodicThread(ConcurrentAVLTreeIntSet o) {
        balanceRunnable = ( ) -> periodicRebalance(o);
        balanceThread = new Thread(balanceRunnable);
        // set the thread to daemon mode so it is cleaned up when the object is gc'd
        balanceThread.setDaemon(true);
        balanceThread.start();
    }

    public void close() {
        destroy = true;
        condition.set(true);
    }

    public boolean addInt(int x) {
        Node addParent = null;

        long stamp = balanceMutex.readLock();

        try {

            retry:
            while (true) {
                Window wnd = findNode(x);

                if (wnd.getChild() != null)
                    return false;
                lockNode(wnd.getGrandParent());
                lockNode(wnd.getParent());
                try {
                    Node curr = wnd.getChild(), parent = wnd.getParent(), gparent = wnd.getGrandParent();

                    if (curr == null) {
                        Window wnd2 = findNode(x);

                        if (wnd2.getGrandParent() != gparent || wnd2.getParent() != parent || wnd2.getChild() != curr)
                            continue retry;

                        Node n = new Node(x, parent);

                        if (!balanceMutex.validate(stamp))
                            continue retry;

                        if (x < parent.getValue() && parent.getLeft() == null)
                            parent.setLeft(n);
                        else if (x > parent.getValue() && parent.getRight() == null)
                            parent.setRight(n);
                        else
                            continue retry;

                        addParent = parent;
                        // break the loop
                        break;
                    }
                } finally {
                    unlockNode(wnd.getGrandParent());
                    unlockNode(wnd.getParent());
                }
            }
        } finally {
           balanceMutex.unlockRead(stamp);
        }

        updates += 1;
        if (updates >= balanceThresh)
            condition.set(true);

        return true;
    }

    public boolean removeInt(int x) {
        Node remParent;

        long stamp = balanceMutex.readLock();

        try {
            retry:
            while (true) {
                // find the node to remove
                Window wnd = findNode(x);

                if (wnd.getChild() == null)
                    return false;

                Node curr = wnd.getChild(), parent = wnd.getParent();
                parent.lock();
                curr.lock();

                try {
                    Window wnd2 = findNode(x);
                    if (wnd2.getParent() != parent || wnd2.getChild() != curr)
                        continue retry;

                    // case 1 - leaf node
                    if (curr.getLeft() == null && curr.getRight() == null) {
                        if (parent.getLeft() == curr) {
                            parent.setLeft(null);
                        } else {
                            parent.setRight(null);
                        }

                        remParent = parent;
                        break;
                    }

                    // case 2 - 1 child node
                    if (curr.getLeft() == null) {
                        if (parent.getLeft() == curr) {
                            parent.setLeft(curr.getRight());
                            parent.getLeft().setParent(parent);
                        } else {
                            parent.setRight(curr.getRight());
                            parent.getRight().setParent(parent);
                        }

                        curr.setRight(null);
                        remParent = parent;
                        break;
                    }

                    if (curr.getRight() == null) {
                        if (parent.getLeft() == curr) {
                            parent.setLeft(curr.getLeft());
                            parent.getLeft().setParent(parent);
                        } else {
                            parent.setRight(curr.getLeft());
                            parent.getRight().setParent(parent);
                        }

                        curr.setLeft(null);
                        remParent = parent;
                        break;
                    }

                    // find the min node in the right subtree
                    Node rightSubtree = curr.getRight();
                    Window wndSubtree = findMinNode(new Window(parent, curr, rightSubtree));
                    Node minNode = wndSubtree.getChild(), minParent = wndSubtree.getParent();

                    try {
                        int minValue = minNode.getValue();
                        Window wnd3 = findNode(minValue);

                        if (wnd3.getParent() == minParent && wnd3.getChild() == minNode) {
                            int oldValue = curr.getValue();
                            curr.setValue(minValue);
                            minNode.setValue(oldValue);

                            // case 3 - 2 child nodes
                            // stupid special case of this
                            if (rightSubtree.getLeft() == null) {
                                curr.setRight(minNode.getRight());
                                if (!curr.isRight(null))
                                    curr.getRight().setParent(curr);

                                minNode.setLeft(null);
                                minNode.setRight(null);

                                remParent = curr;
                                break;
                            }

                            // min node has a right subtree
                            if (minNode.getRight() != null) {
                                // attach the min nodes right subtree to the min nodes parents left subtree
                                minParent.setLeft(minNode.getRight());
                                if (!minParent.isLeft(null))
                                    minParent.getLeft().setParent(minParent);
                            } else {
                                // remove the left subtree from the min nodes parent
                                minParent.setLeft(null);
                            }

                            minNode.setLeft(null);
                            minNode.setRight(null);

                            remParent = minParent;
                            break;
                        }
                    } finally {
                        minParent.unlock();
                        minNode.unlock();
                    }
                } finally {
                    parent.unlock();
                    curr.unlock();
                }
            }
        } finally {
            balanceMutex.unlockRead(stamp);
        }

        updates += 1;

        if (updates >= balanceThresh)
            condition.set(true);

        return true;
    }

    public boolean containsInt(int x) {
        while (true) {
            Window wnd = findNode(x);

            if (wnd.getChild() == null)
                return false;

            Node parent = wnd.getParent(), curr = wnd.getChild();
            // rebalance changed the structure
            if (!curr.isParent(parent) || curr.getBalancing() || parent.getBalancing())
                continue;

            lockNode(parent);
            lockNode(curr);

            try {
                Window wnd2 = findNode(x);
                if (wnd2.getParent() == parent && wnd2.getChild() == curr)
                    return true;

            } finally {
                unlockNode(parent);
                unlockNode(curr);
            }
        }
    }

    public void clear() {
        root.setLeft(null);
        root.setRight(null);
    }

    public int size() {
        Stack<Node> dfs = new Stack<>();
        dfs.push(getRoot());

        int size = 0;

        // do a dfs of the tree to count the nodes
        while (!dfs.empty()) {
            Node curr = dfs.pop();

            if (curr != null) {
                dfs.push(curr.getRight());
                dfs.push(curr.getLeft());
                size += 1;
            }
        }

        return size;
    }

    // return a nodes height
    private int height(Node n) {
        return (n == null) ? 0 : n.getHeight();
    }

    // calculate the balance factor of the node
    private int balanceFactor(Node n) {
        return height(n.getLeft()) - height(n.getRight());
    }

    // get the max height between the left and right children
    private int maxHeight(Node n) {
        return Math.max(height(n.getLeft()), height(n.getRight()));
    }

    /*
     * perform a double right rotation around the subtree rooted at 'a'
     *
     *           a
     *         /
     *       b       ->     b
     *     /              /   \
     *   c               c     a
     */
    private Node rotateRight(Node a) {
        Node b = a.getLeft();
        Node bRight = b.getRight();

         a.setLeft(bRight);

        if (bRight != null)
            bRight.setParent(a);

        b.setRight(a);
        a.setParent(b);

        // fix up the node heights after we've rotated
        a.setHeight(maxHeight(a) + 1);
        b.setHeight(maxHeight(b) + 1);

        return b;
    }

    /*
     * perform a double left rotation around the subtree rooted at 'a'
     *
     *  a
     *    \
     *      b        ->      b
     *        \            /   \
     *          c        a       c
     */
    private Node rotateLeft(Node a) {
        Node b = a.getRight();
        Node bLeft = b.getLeft();

        a.setRight(bLeft);

        if (bLeft != null)
            bLeft.setParent(a);

        b.setLeft(a);
        a.setParent(b);

        // fix up the node heights after we've rotated
        a.setHeight(maxHeight(a) + 1);
        b.setHeight(maxHeight(b) + 1);

        return b;
    }

    /*
     * perform a right rotation around the subtree rooted at the right child
     * then a left rotation around the subtree rooted at 'a'
     */
    private Node rotateRightLeft(Node a) {
        a.setRight(rotateRight(a.getRight()));
        a.getRight().setParent(a);

        return rotateLeft(a);
    }

    /*
     * perform a left rotation around the subtree rooted at the left child
     * then a right rotation around the subtree rooted at 'a'
     */
    private Node rotateLeftRight(Node a) {
        a.setLeft(rotateLeft(a.getLeft()));
        a.getLeft().setParent(a);

        return rotateRight(a);
    }

    private static void periodicRebalance(ConcurrentAVLTreeIntSet o) {
        while (true) {
            try {
                while (!o.condition.get() || !o.destroy)
                    Thread.sleep(1);
            } catch (InterruptedException e) {
                //
            }

            if (o.destroy)
                break;

            if (!o.condition.get() || o.getRoot() == null)
                continue;

            long stamp = o.balanceMutex.writeLock();

            try {
                o.root.setRight(o.rebalance(o.root, o.root.getRight()));
                o.updates = 0;
            } finally {
                o.balanceMutex.unlockWrite(stamp);
                o.condition.set(false);
            }
        }
    }

    private Node rebalance(Node parent, Node n) {
        if (n == null)
            return n;

        n.setLeft(rebalance(n, n.getLeft()));
        n.setRight(rebalance(n, n.getRight()));

        n.setHeight(maxHeight(n) + 1);
        int bf = balanceFactor(n);

        parent.setBalancing(true);
        n.setBalancing(true);

        Node newRoot = null;

        if (bf > 1) {
            if (balanceFactor(n.getLeft()) >= 0)
                newRoot = rotateRight(n);
            else
                newRoot = rotateLeftRight(n);
        } else if (bf < -1) {
            if (balanceFactor(n.getRight()) <= 0)
                newRoot = rotateLeft(n);
            else
                newRoot = rotateRightLeft(n);
        }

        parent.setBalancing(false);
        n.setBalancing(false);

        // fix up parent link if we performed any rotations
        if (newRoot != null) {
            newRoot.setParent(parent);
            return newRoot;
        }

        return n;

    }

    private Window findNode(int x) {
        Node curr = root, parent = null, gparent = null;

        while (curr != null) {
            if (x == curr.getValue())
                break;

            gparent = parent;
            parent = curr;
            curr = (x < curr.getValue()) ? curr.getLeft() : curr.getRight();
        }

        return new Window(gparent, parent, curr);
    }

    private Window findMinNode(Window window) {
        Node curr = window.getChild(), parent = window.getParent(), gparent = window.getGrandParent();

        parent.lock();
        curr.lock();

        while (curr.getLeft() != null) {
            parent.unlock();
            gparent = parent;
            parent = curr;
            curr = curr.getLeft();
            curr.lock();
        }

        return new Window(gparent, parent, curr);
    }

    public void inorderPrint() {
        _inorderPrint(getRoot());
        System.out.printf("\n");
    }

    private void _inorderPrint(Node n) {
        if (n == null) {
            return;
        }

        _inorderPrint(n.getLeft());
        System.out.printf("%d ", n.getValue());
        _inorderPrint(n.getRight());
    }

    public boolean testIntegrity() {
        Node curr = getRoot();
        if (curr == null)
            return true;

        Stack<Node> stack = new Stack<>();
        stack.push(curr);

        while (!stack.empty()) {
            curr = stack.pop();
            Node parent = curr.getParent();

            if (parent != null && !(parent.getLeft() == curr || parent.getRight() == curr))
                return false;

            if (curr.getRight() != null) {
                if (curr.getValue() < curr.getRight().getValue())
                    stack.push(curr.getRight());
                else
                    return false;
            }

            if (curr.getLeft() != null) {
                if (curr.getValue() > curr.getLeft().getValue())
                    stack.push(curr.getLeft());
                else
                    return false;
            }
        }

        return true;
    }

    private Node getRoot() {
        return root.getRight();
    }

    private void lockNode(Node n) {
        if (n == null)
            return;
        n.lock();
    }

    private void unlockNode(Node n) {
        if (n == null)
            return;
        n.unlock();
    }

    class Node {
        private Node left, right, parent;
        private int value;
        // height of the node
        private int height;
        private boolean sentinel;
        private Lock mutex;
        private boolean balancing;

        public Node(int value, Node parent, Node left, Node right, boolean sentinel) {
            this.height = 0;
            this.value = value;
            this.left = left;
            this.right = right;
            this.sentinel = sentinel;
            this.parent = parent;
            this.mutex = new ReentrantLock();
            this.balancing = false;
        }

        public Node(int value, Node parent) { this(value, parent, null, null, false); }
        public Node(int value) {
            this(value, null, null, null, false);
        }

        public Node() {
            this(Integer.MIN_VALUE, null, null, null, true);
        }

        public Node getLeft() { return left; }
        public Node getRight() { return right; }
        public int getValue() { return value; }
        public Node getParent() { return parent; }
        public int getHeight() { return height; }
        public boolean getBalancing() { return balancing; }
        public void setBalancing(boolean flag) { balancing = flag; }
        public void setValue(int x) { value = x; }
        public void setLeft(Node n) { left = n; }
        public void setRight(Node n) { right = n; }
        public void setParent(Node n) { parent = n; }
        public void setHeight(int h) { height = h; }

        // lazy helpers for checking
        public boolean isRight(Node n) { return right == n; }
        public boolean isLeft(Node n) { return left == n; }
        public boolean isParent(Node n) { return parent == n; }

        public void lock() {
            mutex.lock();
        }
        public void unlock() {
            mutex.unlock();
        }
    }

    class Window {
        private Node parent, curr, gparent;

        public Window(Node gparent, Node parent, Node curr) {
            this.gparent = gparent;
            this.parent = parent;
            this.curr = curr;
        }

        public Node getGrandParent() {
            return gparent;
        }

        public Node getParent() {
            return parent;
        }

        public Node getChild() {
            return curr;
        }
    }
}
