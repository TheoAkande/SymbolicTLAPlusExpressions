package tlc2.overrides;

import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.locks.ReentrantLock;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.Values;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueExcept;

import util.Assert;

/* 
    TODO: 
    - Correct tla+ spec for symbolic expressions
*/ 

public abstract class SymbolicExpression extends Value {

    /* --------------------- Operators --------------------- */
    // Empty
    @TLAPlusOperator(identifier = "EMPTY", module = "SymbolicExpression", warn = false)
    public static Value expr() {
        return SymbolicEmpty.getInstance();
    }

    // Construct atomic expression
    @TLAPlusOperator(identifier = "Expr", module = "SymbolicExpression", warn = false)
    public static Value expr(final Value atom) {
        return SymbolicAtom.generate(atom); // Constructor will handle if atom is not a string
    }

    // e1 == e2
    @TLAPlusOperator(identifier = "Equal", module = "SymbolicExpression", warn = false)
    public static Value equal(final Value e1, final Value e2) {
        if (!(e1 instanceof SymbolicExpression && e2 instanceof SymbolicExpression)) {
            Assert.fail("Attempted to compare equality with non-symbolic expression");
            return BoolValue.ValFalse;
        }

        final SymbolicExpression s1 = (SymbolicExpression) e1;
        final SymbolicExpression s2 = (SymbolicExpression) e2;

        if (!(s1.isSumExpr() && s2.isSumExpr())) {
            return s1.equals(s2) ? BoolValue.ValTrue : BoolValue.ValFalse;
        }

        final SymbolicSum sum1 = (SymbolicSum) s1;
        final SymbolicSum sum2 = (SymbolicSum) s2;

        final Map<SymbolicExpression, Integer> s1Bag = sum1.getBag();
        final Map<SymbolicExpression, Integer> s2Bag = sum2.getBag();

        final Set<SymbolicExpression> s1KeySet = s1Bag.keySet();
        final Set<SymbolicExpression> s2KeySet = s2Bag.keySet();

        if (sum1.getCardinality() != sum2.getCardinality() || s1KeySet.size() != s2KeySet.size()) {
            return BoolValue.ValFalse;
        }

        final BitSet keysSeen = new BitSet(s1KeySet.size());

        for (final SymbolicExpression checkExp1 : s1KeySet) {
            int index = 0;
            boolean valid = false;
            // Assuming we iterate through keyset in the same order each time (check this)
            for (final SymbolicExpression checkExp2 : s2KeySet) {
                if (!keysSeen.get(index) && checkExp1.equals(checkExp2)) {
                    keysSeen.set(index);
                    valid = true;
                    break;
                }
                index++;
            }
            if (!valid) {
                return BoolValue.ValFalse;
            }
        }
        return BoolValue.ValTrue;
    }

    // e1 <= e2
    @TLAPlusOperator(identifier = "LE", module = "SymbolicExpression", warn = false)
    public static Value lessThanEqual(final Value e1, final Value e2) {
        if (!(e1 instanceof SymbolicExpression && e2 instanceof SymbolicExpression)) {
            Assert.fail("Attempted to compare LE with non-symbolic expression");
            return BoolValue.ValFalse;
        }

        final SymbolicExpression exp1 = (SymbolicExpression) e1;
        final SymbolicExpression exp2 = (SymbolicExpression) e2;

        return SymbolicExpression.le(exp1, exp2) ? BoolValue.ValTrue : BoolValue.ValFalse;
    }

    // e1 + e2
    @TLAPlusOperator(identifier = "Add", module = "SymbolicExpression", warn = false)
    public static Value add(final Value e1, final Value e2) {
        if (!(e1 instanceof SymbolicExpression && e2 instanceof SymbolicExpression)) {
            Assert.fail("Attempted to sum with non-symbolic expression");
            return SymbolicEmpty.getInstance();
        }

        final SymbolicExpression s1 = (SymbolicExpression) e1;
        final SymbolicExpression s2 = (SymbolicExpression) e2;

        if (s1.isEmptyExpr()) {
            return s2;
        }

        if (s2.isEmptyExpr()) {
            return s1;
        }

        if (s1.isSumExpr() && s2.isSumExpr()) {
            SymbolicSum sum1 = (SymbolicSum) s1;
            final SymbolicSum sum2 = (SymbolicSum) s2;
            for (final Map.Entry<SymbolicExpression, Integer> entry : sum2.getBag().entrySet()) {
                sum1 = sum1.addTo(entry.getKey(), entry.getValue());
            }
            return sum1;
        }

        if (s1.isSumExpr()) {
            return ((SymbolicSum) s1).addTo(s2);
        }

        if (s2.isSumExpr()) {
            return ((SymbolicSum) s2).addTo(s1);
        }

        return SymbolicSum.generate(new HashMap<>()).addTo(s1).addTo(s2);
    }

    // e1 x n
    @TLAPlusOperator(identifier = "Mult", module = "SymbolicExpression", warn = false)
    public static Value mult(final Value e1, final Value e2) {
        if (!(e1 instanceof SymbolicExpression && e2 instanceof IntValue)) {
            Assert.fail("Attempted to multiply with non-symbolic expression");
            return SymbolicEmpty.getInstance();
        }

        final SymbolicExpression s = (SymbolicExpression) e1;
        final int factor = ((IntValue) e2).val;

        if (s.isEmptyExpr() || factor == 0) {
            return SymbolicEmpty.getInstance();
        }

        if (factor == 1) {
            return s;
        }

        if (s.isSumExpr()) {
            final SymbolicSum sum = (SymbolicSum) s;
            SymbolicSum ret = sum;
            for (final Map.Entry<SymbolicExpression, Integer> entry : sum.getBag().entrySet()) {
                ret = ret.addTo(entry.getKey(), entry.getValue() * (factor - 1));
            }
            return ret;
        }

        return SymbolicSum.generate(Map.of(s, 1)).addTo(s, factor - 1);
    }

    // max(e1, e2)
    @TLAPlusOperator(identifier = "Max", module = "SymbolicExpression", warn = false)
    public static Value max(final Value e1, final Value e2) {
        if (!(e1 instanceof SymbolicExpression && e2 instanceof SymbolicExpression)) {
            Assert.fail("Attempted to apply max between with non-symbolic expressions");
            return SymbolicEmpty.getInstance();
        }

        final SymbolicExpression s1 = (SymbolicExpression) e1;
        final SymbolicExpression s2 = (SymbolicExpression) e2;

        if (SymbolicExpression.le(s1, s2)) {
            return s2;
        }
        if (SymbolicExpression.le(s2, s1)) {
            return s1;
        }

        if (s1.isSumExpr() && s2.isSumExpr()) {
            final SymbolicSum[] split = SymbolicSum.split((SymbolicSum)s1, (SymbolicSum)s2);
            final SymbolicMax m = SymbolicMax.generate(split[1].extract(), split[2].extract());
            if (split[0].getCardinality() == 0) {
                return m;
            }
            return split[0].addTo(m);
        }

        return SymbolicMax.generate(s1, s2);
    }

    protected static final Set<SymbolicExpression> emptySet = new HashSet<>();
    protected static ConcurrentHashMap<SymbolicExpression, SymbolicExpression> canonicalMap = new ConcurrentHashMap<>();
    private static final ReentrantLock generationLock = new ReentrantLock();

    protected static void acquireGenerationLock() {
        SymbolicExpression.generationLock.lock();
    }

    protected static void releaseGenerationLock() {
        SymbolicExpression.generationLock.unlock();
    }

    protected static void addExpression(final SymbolicExpression e) {
        SymbolicExpression.canonicalMap.put(e, e);
    }

    protected static SymbolicExpression get(final SymbolicExpression e) {
        return canonicalMap.get(e);   
    }

    protected static Set<SymbolicExpression> getAll() {
        return SymbolicExpression.canonicalMap.keySet();
    }

    protected static boolean le(final SymbolicExpression e1, final SymbolicExpression e2) {
        if (e1.isEmptyExpr()) {
            return true;
        }

        return e2.le.contains(e1) || e1.ge.contains(e2);
    }

    /* --------------------- Value --------------------- */
    // TODO: Override regular toStrings

    private long zeroFingerprintCache;
    private boolean zeroFingerprintSet = false;
    private final Set<SymbolicExpression> le = ConcurrentHashMap.newKeySet(); // All expressions e s.t. e <= this 
    private final Set<SymbolicExpression> ge = ConcurrentHashMap.newKeySet(); // All expressions e s.t. e >= this
    protected final Set<SymbolicAtom> atoms = new HashSet<>();

    protected abstract Map<SymbolicExpression, Integer> getValue();
    protected boolean isEmptyExpr() {return false;}
    protected boolean isAtomExpr() {return false;}
    protected boolean isMaxExpr() {return false;}
    protected boolean isSumExpr() {return false;}

    @Override
    public int compareTo(Object other) {
        try {
            if (other instanceof SymbolicExpression) {
                final SymbolicExpression symOther = (SymbolicExpression) other;
                if (this.equals(other)) {
                    return 0;
                // }
                // if (((BoolValue)SymbolicExpression.lessThanEqual(this, symOther)).val) {
                //     // this is less
                //     return -1;
                // } else if (((BoolValue)SymbolicExpression.lessThanEqual(symOther, this)).val) {
                //     // other is less
                //     return 1;
                } else {
                    // unknown
                    return Long.compare(this.getZeroFingerprint(), symOther.getZeroFingerprint());
                }
            } else {
                Assert.fail("Attempted to compare the symbolic expression " + Values.ppr(this.toString()) +
                " with non-symbolic expression " + other.toString(), getSource());
                return 0;
            }
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) { throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    public boolean isDefined() {
        return true; // TODO: Check what this is used for
    }

    @Override
    public boolean isFinite() {
        try {
            Assert.fail("Attempted to check if the symbolic expression " + Values.ppr(this.toString()) +
            " is a finite set.", getSource());
            return false;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) { throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    public boolean isNormalized() {
        return true; // Normalized by default
    }

    @Override
    public int size() {
        try {
            Assert.fail("Attempted to compute the number of elements in the symbolic expression " +
            Values.ppr(this.toString()) + ".", getSource());
            return 0;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    public byte getKind() {
        return 11; // "a java method" seems the most sensible
    }

    @Override
    public boolean member(Value elem) {
        try {
            Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
            "\nis an element of the symbolic expression " + Values.ppr(this.toString()), getSource());
            return false;     // make compiler happy
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    public Value normalize() {
        return this; // Do nothing
    }

    @Override
    public Value takeExcept(ValueExcept ex) {
        try {
            if (ex.idx < ex.path.length) {
                Assert.fail("Attempted to apply EXCEPT construct to the symbolic expression " +
                Values.ppr(this.toString()) + ".", getSource());
            }
            return ex.value;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    public Value takeExcept(ValueExcept[] exs) {
        try {
            if (exs.length != 0) {
                Assert.fail("Attempted to apply EXCEPT construct to the symbolic expression " +
                Values.ppr(this.toString()) + ".", getSource());
            }
            return this;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    public long fingerPrint(long fp) {
        try {
            if (fp == FP64.Zero) {
                return this.getZeroFingerprint();
            }
            return this.getFullFingerprint(fp);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    // TODO: does this need to be synchronized?
    // We override fingerPrint rather than hashCode for TLC values
    protected long getZeroFingerprint() {
        if (!this.zeroFingerprintSet) {
            this.zeroFingerprintCache = this.getFullFingerprint(FP64.Zero);
            this.zeroFingerprintSet = true;
        }
        return this.zeroFingerprintCache;
    }

    protected void setLessThan(final SymbolicExpression greater) {
        this.ge.add(greater);
    }

    protected void setGreaterThan(final SymbolicExpression less) {
        this.le.add(less);
    }

    protected Set<SymbolicExpression> getAllLE() {
        return this.le;
    }

    protected Set<SymbolicExpression> getAllGE() {
        return this.ge;
    }

    protected abstract long getFullFingerprint(long fp);
}
