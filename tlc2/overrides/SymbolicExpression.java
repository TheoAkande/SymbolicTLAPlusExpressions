package tlc2.overrides;

import java.util.Map;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.Values;
import tlc2.value.impl.BoolValue;
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
        return null; // TODO: Implement correctly
    }

    // e1 == e2
    @TLAPlusOperator(identifier = "Equal", module = "SymbolicExpression", warn = false)
    public static Value equal(final Value e1, final Value e2) {
        return BoolValue.ValFalse; // TODO: Implement correctly
    }

    // e1 <= e2
    @TLAPlusOperator(identifier = "LE", module = "SymbolicExpression", warn = false)
    public static Value lessThanEqual(final Value e1, final Value e2) {
        return BoolValue.ValFalse; // TODO: Implement correctly
    }

    // e1 + e2
    @TLAPlusOperator(identifier = "Add", module = "SymbolicExpression", warn = false)
    public static Value add(final Value e1, final Value e2) {
        return null; // TODO: Implement correctly
    }

    // e1 x n
    @TLAPlusOperator(identifier = "Mult", module = "SymbolicExpression", warn = false)
    public static Value mult(final Value e1, final Value e2) {
        return null; // TODO: Implement correctly
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
