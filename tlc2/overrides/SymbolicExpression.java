package tlc2.overrides;

import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;

import tlc2.tool.EvalControl;
import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.Values;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.EnumerableValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueExcept;

import util.Assert;

/* 
    TODO: 
        - Zero fingerprint cache (since immutable)
        - Stop with all the deep copies (everything should be immutable so should have no need for that)
*/ 

public abstract class SymbolicExpression extends Value {

    /* --------------------- Operators --------------------- */
    // Empty
    @TLAPlusOperator(identifier = "EMPTY", module = "SymbolicExpression", warn = false)
    public static Value expr() {
        return new SymbolicEmpty();
    }

    // Construct atomic expression
    @TLAPlusOperator(identifier = "Expr", module = "SymbolicExpression", warn = false)
    public static Value expr(final Value atom) {
        return new SymbolicAtom(atom); // Constructor will handle if atom is not a string
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
    public static Value lessThanEqual(final Value e1, final Value e2, final Value ltRelation) {
        if (!(e1 instanceof SymbolicExpression && e2 instanceof SymbolicExpression)) {
            Assert.fail("Attempted to compare LE with non-symbolic expression");
            return BoolValue.ValFalse;
        }

        final SymbolicExpression exp1 = (SymbolicExpression) e1;
        final SymbolicExpression exp2 = (SymbolicExpression) e2;

        return SymbolicExpression.le(exp1, exp2, ltRelation) ? BoolValue.ValTrue : BoolValue.ValFalse;
    }

    // e1 + e2
    @TLAPlusOperator(identifier = "Add", module = "SymbolicExpression", warn = false)
    public static Value add(final Value e1, final Value e2) {
        if (!(e1 instanceof SymbolicExpression && e2 instanceof SymbolicExpression)) {
            Assert.fail("Attempted to sum with non-symbolic expression");
            return new SymbolicEmpty();
        }

        final SymbolicExpression s1 = (SymbolicExpression) (e1.deepCopy());
        final SymbolicExpression s2 = (SymbolicExpression) (e2.deepCopy());

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

        final Map<SymbolicExpression, Integer> newBag = new HashMap<>();
        newBag.put(s1, 1);
        newBag.put(s2, newBag.getOrDefault(s2, 0) + 1);
        return new SymbolicSum(newBag);
    }

    // e1 x n
    @TLAPlusOperator(identifier = "Mult", module = "SymbolicExpression", warn = false)
    public static Value mult(final Value e1, final Value e2) {
        if (!(e1 instanceof SymbolicExpression && e2 instanceof IntValue)) {
            Assert.fail("Attempted to multiply with non-symbolic expression");
            return new SymbolicEmpty();
        }

        final SymbolicExpression s = (SymbolicExpression) (e1.deepCopy());
        final int factor = ((IntValue) e2).val;

        if (s.isEmptyExpr() || factor == 0) {
            return new SymbolicEmpty();
        }

        if (factor == 1) {
            return s;
        }

        if (s.isSumExpr()) {
            final SymbolicSum sum = (SymbolicSum) s;
            final Map<SymbolicExpression, Integer> newBag = new HashMap<>();
            for (final Map.Entry<SymbolicExpression, Integer> entry : sum.getBag().entrySet()) {
                newBag.put(entry.getKey(), entry.getValue() * factor);
            }
            return new SymbolicSum(newBag);
        }

        return new SymbolicSum(Map.of(s, factor));
    }

    // max(e1, e2)
    @TLAPlusOperator(identifier = "Max", module = "SymbolicExpression", warn = false)
    public static Value max(final Value e1, final Value e2, final Value ltRelation) {
        return (Value) e1.deepCopy(); // TODO: Implement correctly
    }

    private static AtomicBoolean ltStarted;
    private static AtomicBoolean ltReady;
    private static HashMap<Value, Set<Value>> ltRelation = new HashMap<>();
    // In order to do (more) efficient LE checks, we construct the relation for each expression as it is created.
    private static HashMap<SymbolicExpression, Set<SymbolicExpression>> leRelation = new HashMap<>();

    private static boolean le(final SymbolicExpression e1, final SymbolicExpression e2, final Value ltRelation) {
        if (e1.isEmptyExpr()) {
            return true;
        }

        if (e1.isAtom() & e2.isAtom()) {
            return SymbolicExpression.atomicCompare(e1, e2, ltRelation) < 1;
        }

        if (e1.isMaxExpr() & e2.isMaxExpr()) {
            final SymbolicMax m1 = (SymbolicMax) e1;
            final SymbolicMax m2 = (SymbolicMax) e2;
            return (le(m1.first(), m2.first(), ltRelation) && le(m1.second(), m2.second(), ltRelation)) ||
                (le(m1.first(), m2.second(), ltRelation) && le(m1.second(), m2.second(), ltRelation)) ||
                (le(m1.first(), m2.first(), ltRelation) && le(m1.second(), m2.first(), ltRelation)) ||
                (le(m1.first(), m2.second(), ltRelation) && le(m1.second(), m2.first(), ltRelation));
        }

        if (e2.isMaxExpr()) {
            final SymbolicMax m2 = (SymbolicMax) e2;
            return le(e1, m2.first(), ltRelation) || le(e1, m2.second(), ltRelation);
        }

        if (e1.isMaxExpr()) {
            final SymbolicMax m1 = (SymbolicMax) e1;
            return le(m1.first(), e2, ltRelation) || le(m1.second(), e2, ltRelation);
        }

        if (e1.isSumExpr() & e2.isSumExpr()) {
            return SymbolicExpression.subset((SymbolicSum)e1.deepCopy(), (SymbolicSum)e2.deepCopy(), ltRelation);
        }

        if (e1.isSumExpr() & e2.isAtom()) {
            // TODO: Finish
            return false;
        }

        if (e1.isSumExpr() & e2.isMaxExpr()) {
            // TODO: Finish
            return false;
        }

        if (e1.isAtom() & e2.isSumExpr()) {
            // TODO: Finish
            return false; 
        }

        if (e1.isMaxExpr() & e2.isSumExpr()) {
            // TODO: Finish
            return false;
        }

        return false;
    }

    private static boolean subset(final SymbolicSum s1, final SymbolicSum s2, final Value ltRelation) {
        final Map<SymbolicExpression, Integer> s1b = s1.getBag();
        final Map<SymbolicExpression, Integer> s2b = s2.getBag();

        for (final SymbolicExpression e : s1b.keySet()) {
            if (s2b.containsKey(e)) {
                final int s1v = s1b.get(e);
                final int s2v = s2b.get(e);
                s1b.put(e, s1v < s2v ? 0 : s1v - s2v);
                s2b.put(e, s1v < s2v ? s2v - s1v : 0);
            }
        }
        s1b.values().removeIf(v -> v == 0);
        s2b.values().removeIf(v -> v == 0);

        if (s1b.isEmpty()) {
            return true;
        }

        // TODO: finish
        return false;
    }

    private static int atomicCompareRelationSet(final Value a1, final Value a2) {
        if (!SymbolicExpression.ltReady.get()) {
            Assert.fail("Attempted atomic compare when relation not ready");
            return 2;
        }

        if (!(a1 instanceof SymbolicAtom && a2 instanceof SymbolicAtom)) {
            Assert.fail("Attempted to compare atoms that are not atoms or not function");
            return 2;
        }
        if (a1.equals(a2)) {
            return 0;
        }
        if (SymbolicExpression.ltRelation.get(a1).contains(a2)) {
            return -1;
        }
        if (SymbolicExpression.ltRelation.get(a2).contains(a1)) {
            return 1;
        }
        return 2;
    }

    private static int atomicCompare(final Value a1, final Value a2, final Value lessThanRelation) {
        if (!(a1 instanceof SymbolicAtom && a2 instanceof SymbolicAtom && lessThanRelation instanceof EnumerableValue)) {
            Assert.fail("Attempted to compare atoms that are not atoms or not function");
            return 2;
        }
        
        if (a1.equals(a2)) {
            return 0;
        }
        while (SymbolicExpression.ltStarted.get()) {
            if (SymbolicExpression.ltReady.get()) {
                return SymbolicExpression.atomicCompareRelationSet(a1, a2);
            }
            Thread.onSpinWait();
        }

        if (!SymbolicExpression.ltStarted.compareAndSet(false, true)) {
            return SymbolicExpression.atomicCompare(a1, a2, lessThanRelation);
        }

        if (!(lessThanRelation instanceof EnumerableValue)) {
            Assert.fail("LTRelation is not an enumerable val?");
            return 2;
        }
        final EnumerableValue ltRelation = (EnumerableValue) lessThanRelation;
        final Set<Value> domain = new HashSet<>(ltRelation.elements().all());
        final Set<Value> atoms = new HashSet<>();
        for (final Value e : domain) {
            if (!(e instanceof TupleValue)) {
                Assert.fail("Domain items are not tuples");
                return 2;
            }
            final Value less = ((TupleValue)e).apply(IntValue.gen(1), EvalControl.KeepLazy);
            final Value more = ((TupleValue)e).apply(IntValue.gen(2), EvalControl.KeepLazy);
            atoms.add(less);
            atoms.add(more);
            final Set<Value> ltForA = SymbolicExpression.ltRelation.computeIfAbsent(less, x -> new HashSet<>());
            ltForA.add(more);
        }

        boolean changed = true;
        while (changed) {
            changed = false;
            for (final Value a : atoms) {
                final Set<Value> ltForA = SymbolicExpression.ltRelation.computeIfAbsent(a, x -> new HashSet<>());
                final int sizeBefore = ltForA.size();
                for (final Value aPrime : ltForA) {
                    ltForA.addAll(SymbolicExpression.ltRelation.get(aPrime));
                }
                changed |= sizeBefore != ltForA.size();
            }
        }

        SymbolicExpression.ltReady.set(true);
        return SymbolicExpression.atomicCompare(a1, a2, lessThanRelation);
    }

    /* --------------------- Value --------------------- */
    // TODO: Override regular toStrings

    protected abstract Map<SymbolicExpression, Integer> getValue();
    protected boolean isEmptyExpr() {return false;}
    protected boolean isAtomExpr() {return false;}
    protected boolean isMaxExpr() {return false;}
    protected boolean isSumExpr() {return false;}
    private long zeroFingerprintCache;
    private boolean zeroFingerprintSet = false;

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
            this.zeroFingerprintCache = this.fingerPrint(FP64.Zero);
            this.zeroFingerprintSet = true;
        }
        return this.zeroFingerprintCache;
    }


    protected abstract long getFullFingerprint(long fp);
}
