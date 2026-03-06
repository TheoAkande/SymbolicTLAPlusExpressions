package tlc2.overrides;

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
    - Fix the hanging
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

        return s1.equals(s2) ? BoolValue.ValTrue : BoolValue.ValFalse;
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

        // System.out.println(exp1.toString() + " <= " + exp2.toString());
        // System.out.println(SymbolicExpression.le(exp1, exp2));
        return SymbolicExpression.le(exp1, exp2) == TRUE ? BoolValue.ValTrue : BoolValue.ValFalse;
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

        if (le(s1, s2) == TRUE) {
            return s2;
        }
        if (le(s2, s1) == TRUE) {
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
    protected static final ConcurrentHashMap<SymbolicExpression, SymbolicExpression> canonicalMap = new ConcurrentHashMap<>();
    private static final ReentrantLock generationLock = new ReentrantLock();
    private static final int TRUE = 1;
    private static final int FALSE = 0;
    private static final int UNKNOWN = -1;

    protected static void acquireGenerationLock() {
        generationLock.lock();
    }

    protected static void releaseGenerationLock() {
        generationLock.unlock();
    }

    protected static void addExpression(final SymbolicExpression e) {
        canonicalMap.put(e, e);
        final Set<SymbolicExpression> existingKeys = new HashSet<>(canonicalMap.keySet());
        for (final SymbolicExpression o : existingKeys) {
            if (o != e) compareExprs(e, o);
        }
    }

    protected static SymbolicExpression get(final SymbolicExpression e) {
        return canonicalMap.get(e);   
    }

    protected static Set<SymbolicExpression> getAll() {
        return canonicalMap.keySet();
    }

    protected static int le(final SymbolicExpression e1, final SymbolicExpression e2) {
        if (e1.equals(e2)) {
            return TRUE;
        }
        acquireGenerationLock();
        try{
            compareExprs(e1, e2);
            
            return e1.thisLessThan.get(e2);
        } finally {
            releaseGenerationLock();
        }
    }

    private static void compareAtomSum(final SymbolicAtom a, final SymbolicSum s) {
        if (s.getCardinality() == 0) {
            a.thisLessThan.put(s, FALSE);
            s.thisLessThan.put(a, TRUE);
            return;
        }
        if (s.atoms.contains(a)) {
            a.thisLessThan.put(s, s.getCardinality() == 1 ? FALSE : TRUE);
            s.thisLessThan.put(a, FALSE);
            return;
        } 

        a.thisLessThan.put(s, UNKNOWN);
        s.thisLessThan.put(a, UNKNOWN);
    }

    private static void compareAtomMax(final SymbolicAtom a, final SymbolicMax m) {
        a.thisLessThan.put(m, m.atoms.contains(a) ? TRUE : UNKNOWN);
        m.thisLessThan.put(a, m.atoms.contains(a) ? FALSE : UNKNOWN);
    }

    private static void compareSumSum(final SymbolicSum s1, final SymbolicSum s2) {
        final SymbolicSum[] apart = SymbolicSum.split(s1, s2); // Extract out the common base

        final SymbolicSum sum1 = apart[1];
        final SymbolicSum sum2 = apart[2];

        if (apart[0].getCardinality() > 0) {
            compareExprs(sum1, sum2);
            s1.thisLessThan.put(s2, sum1.thisLessThan.get(sum2));
            s2.thisLessThan.put(s1, sum2.thisLessThan.get(sum1));
            return;
        }

        // s1 == sum1, s2 == sum2

        final int s1c = s1.getCardinality();
        final int s2c = s2.getCardinality();
        if (s1c * s2c == 0) {
            s1.thisLessThan.put(s2, s2c > s1c ? TRUE : FALSE);
            s2.thisLessThan.put(s1, s1c > s2c ? TRUE : FALSE);
            return;
        }

        boolean containsMax = false;
        for (final SymbolicExpression e : s1.getBag().keySet()) {
            containsMax |= e.isMaxExpr();
        }
        for (final SymbolicExpression e : s2.getBag().keySet()) {
            containsMax |= e.isMaxExpr();
        }
        if (!containsMax) { // Incomparable atoms
            s1.thisLessThan.put(s2, UNKNOWN); 
            s2.thisLessThan.put(s1, UNKNOWN);
            return;
        }

        final Set<SymbolicExpression> flat1 = sum1.flatten();
        final Set<SymbolicExpression> flat2 = sum2.flatten();

        // s1 < s2:
        boolean less = true;
        for (final SymbolicExpression e1 : flat1) { // For each in flat1
            boolean found = false;
            for (final SymbolicExpression e2 : flat2) { // Exists in flat2
                if (le(e1, e2) == TRUE) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                less = false;
                break;
            }
        }
        if (less) {
            s1.thisLessThan.put(s2, TRUE);
            s2.thisLessThan.put(s1, FALSE);
            return;
        }

        // s2 < s1:
        less = true;
        for (final SymbolicExpression e2 : flat2) { // For each in flat2
            boolean found = false;
            for (final SymbolicExpression e1 : flat1) { // Exists in flat1
                if (le(e2, e1) == TRUE) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                less = false;
                break;
            }
        }
        if (less) {
            s1.thisLessThan.put(s2, FALSE);
            s2.thisLessThan.put(s1, TRUE);
            return;
        }

        s1.thisLessThan.put(s2, UNKNOWN);
        s2.thisLessThan.put(s1, UNKNOWN);
    }

    private static void compareSumMax(final SymbolicSum s, final SymbolicMax m) {
        // s < m
        if (le(s, m.first()) == TRUE && le(s, m.second()) == TRUE) {
            s.thisLessThan.put(m, TRUE);
            m.thisLessThan.put(s, FALSE);
            return;
        }
        // m < s
        if (le(m.first(), s) == TRUE || le(m.second(), s) == TRUE) {
            s.thisLessThan.put(m, FALSE);
            m.thisLessThan.put(s, TRUE);
            return;
        }

        s.thisLessThan.put(m, UNKNOWN);
        m.thisLessThan.put(s, UNKNOWN);
    }

    private static void compareMaxMax(final SymbolicMax m1, final SymbolicMax m2) {
        // m1 < m2
        if (
            (le(m1.first(), m2.first()) == TRUE || le(m1.first(), m2.second()) == TRUE) &&
            (le(m1.second(), m2.first()) == TRUE || le(m1.second(), m2.second()) == TRUE)
        ) {
            m1.thisLessThan.put(m2, TRUE);
            m2.thisLessThan.put(m1, FALSE);
            return;
        }
        // m2 < m1
        if (
            (le(m2.first(), m1.first()) == TRUE || le(m2.first(), m1.second()) == TRUE) &&
            (le(m2.second(), m1.first()) == TRUE || le(m2.second(), m1.second()) == TRUE)
        ) {
            m1.thisLessThan.put(m2, FALSE);
            m2.thisLessThan.put(m1, TRUE);
            return;
        }

        m1.thisLessThan.put(m2, UNKNOWN);
        m2.thisLessThan.put(m1, UNKNOWN);
    }

    private static void compareExprs(final SymbolicExpression e1, final SymbolicExpression e2) {
        if (e1.thisLessThan.contains(e2)) {
            return;
        }

        if (e1.equals(e2)) {
            e1.thisLessThan.put(e2, FALSE);
            e2.thisLessThan.put(e1, FALSE);
            return;
        }

        if (e1.isEmptyExpr()) {
            e1.thisLessThan.put(e2, e2.isEmptyExpr() ? FALSE : TRUE);
            e2.thisLessThan.put(e1, FALSE);
            return;
        }

        if (e2.isEmptyExpr()) {
            e2.thisLessThan.put(e1, TRUE);
            e1.thisLessThan.put(e2, FALSE);
            return;
        }

        if (e1.isAtomExpr() && e2.isAtomExpr()) {
            e1.thisLessThan.put(e2, UNKNOWN);
            e2.thisLessThan.put(e1, UNKNOWN);
            return;
        }

        if (e1.isAtomExpr() && e2.isSumExpr()) {
            compareAtomSum((SymbolicAtom) e1, (SymbolicSum) e2);
            return;
        }

        if (e2.isAtomExpr() && e1.isSumExpr()) {
            compareAtomSum((SymbolicAtom) e2, (SymbolicSum) e1);
            return;
        }

        if (e1.isAtomExpr() && e2.isMaxExpr()) {
            compareAtomMax((SymbolicAtom) e1, (SymbolicMax) e2);
        }

        if (e2.isAtomExpr() && e1.isMaxExpr()) {
            compareAtomMax((SymbolicAtom) e2, (SymbolicMax) e1);
        }

        if (e1.isSumExpr() && e2.isSumExpr()) {
            compareSumSum((SymbolicSum) e1, (SymbolicSum) e2);
            return;
        }

        if (e1.isSumExpr() && e2.isMaxExpr()) {
            compareSumMax((SymbolicSum) e1, (SymbolicMax) e2);
            return;
        }

        if (e2.isSumExpr() && e1.isMaxExpr()) {
            compareSumMax((SymbolicSum) e2, (SymbolicMax) e1);
            return;
        }

        if (e1.isMaxExpr() && e2.isMaxExpr()) {
            compareMaxMax((SymbolicMax) e1, (SymbolicMax) e2);
            return;
        }
    }

    /* --------------------- Value --------------------- */
    private long zeroFingerprintCache;
    private boolean zeroFingerprintSet = false;
    protected final ConcurrentHashMap<SymbolicExpression, Integer> thisLessThan = new ConcurrentHashMap<>();
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
                } else {
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

    protected abstract void setup();

    protected long getZeroFingerprint() {
        if (!this.zeroFingerprintSet) {
            this.zeroFingerprintCache = this.getFullFingerprint(FP64.Zero);
            this.zeroFingerprintSet = true;
        }
        return this.zeroFingerprintCache;
    }

    protected abstract long getFullFingerprint(long fp);
}
