package tlc2.overrides;

import java.util.HashMap;
import java.util.Map;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.IValue;
import tlc2.value.impl.BoolValue;

public class SymbolicSum extends SymbolicExpression {

    private final Map<SymbolicExpression, Integer> bag = new HashMap<>();

    public SymbolicSum() {
        // Do nothing for now?
    }

    public SymbolicExpression add(final SymbolicExpression e) {
        try {
            this.bag.put(e, this.bag.getOrDefault(e, 0) + 1);
            return this;
        } catch (final RuntimeException | OutOfMemoryError err) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, err);}
            else {throw err;}
        }
    }

    public SymbolicExpression add(final SymbolicExpression e, final int num) {
        try {
            this.bag.put(e, this.bag.getOrDefault(e, 0) + num);
            return this;
        } catch (final RuntimeException | OutOfMemoryError err) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, err);}
            else {throw err;}
        }
    }

    @Override
    protected boolean isSumExpr() {return true;}

    @Override
    public IValue deepCopy() {
        try {
            final SymbolicSum ret = new SymbolicSum();
            for (SymbolicExpression e : this.bag.keySet()) {
                ret.add((SymbolicExpression) e.deepCopy(), this.bag.get(e));
            }
            return ret;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    public StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
        try {
            int index = 0;
            for (final SymbolicExpression e : this.bag.keySet()) {
                e.toString(sb, offset, swallow);
                if (this.bag.get(e) > 1) {
                    sb.append(" x " + this.bag.get(e));
                }
                if (index < this.bag.keySet().size() - 1) {
                    sb.append(" + ");
                }
                index++;
            } 
            return sb;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    protected Map<SymbolicExpression, Integer> getValue() {
        return this.bag;
    }
    
    @Override
    public boolean equals(final Object other) {
        try {
            if (other instanceof SymbolicSum) {
                final SymbolicSum sumOther = (SymbolicSum) other;
                return ((BoolValue)SymbolicExpression.equal(this, sumOther)).val;
            }
            return false;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    // We override fingerPrint rather than hashCode for TLC values
    @Override
    public long fingerPrint(long fp) {
        try {
            fp = FP64.Extend(fp, "SUM");
            for (final SymbolicExpression e : this.bag.keySet()) {
                fp = FP64.Extend(fp, e.fingerPrint(FP64.Zero));
                fp = FP64.Extend(fp, FP64.Hash(this.bag.get(e)));
            }
            return fp;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }
}
