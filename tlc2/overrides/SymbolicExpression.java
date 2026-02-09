package tlc2.overrides;

import java.util.BitSet;
import java.util.EmptyStackException;
import java.util.Map;
import java.util.Set;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.Values;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueExcept;

import util.Assert;

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
    public static Value lessThanEqual(final Value e1, final Value e2) {
        return BoolValue.ValFalse; // TODO: Implement correctly
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

        if (s1.isEmpty()) {
            return s2;
        }

        if (s2.isEmpty()) {
            return s1;
        }

        if (s1.isSumExpr() && s2.isSumExpr()) {
            final SymbolicSum sum1 = (SymbolicSum) s1;
            final SymbolicSum sum2 = (SymbolicSum) s2;
            for (final Map.Entry<SymbolicExpression, Integer> entry : sum2.getBag().entrySet()) {
                sum1.add(entry.getKey(), entry.getValue()); // Should be safe because we overrode equals/fingerprint
            }
            return sum1;
        }

        if (s1.isSumExpr()) {
            ((SymbolicSum) s1).add(s2);
            return s1;
        }

        if (s2.isSumExpr()) {
            ((SymbolicSum) s2).add(s1);
            return s2;
        }

        final SymbolicSum ret = new SymbolicSum();
        ret.add(s1);
        ret.add(s2);

        return ret;
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

        if (s.isEmpty() || factor == 0) {
            return new SymbolicEmpty();
        }

        if (factor == 1) {
            return s;
        }

        if (s.isSumExpr()) {
            final SymbolicSum sum = (SymbolicSum) s;
            for (final Map.Entry<SymbolicExpression, Integer> entry : sum.getBag().entrySet()) {
                sum.getBag().put(entry.getKey(), entry.getValue() * factor);
            }
            return sum;
        }

        final SymbolicSum ret = new SymbolicSum();
        ret.add(s, factor);
        return ret;
    }

    // max(e1, e2)
    @TLAPlusOperator(identifier = "Max", module = "SymbolicExpression", warn = false)
    public static Value max(final Value e1, final Value e2) {
        return null; // TODO: Implement correctly
    }

    /* --------------------- Value --------------------- */
    // TODO: Override regular toStrings

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
                }
                if (((BoolValue)SymbolicExpression.lessThanEqual(this, symOther)).val) {
                    // this is less
                    return -1;
                } else if (((BoolValue)SymbolicExpression.lessThanEqual(symOther, this)).val) {
                    // other is less
                    return 1;
                } else {
                    // unknown
                    return Long.compare(this.fingerPrint(FP64.Zero), symOther.fingerPrint(FP64.Zero));
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
}
