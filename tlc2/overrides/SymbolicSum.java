package tlc2.overrides;

import java.util.HashMap;
import java.util.Map;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.IValue;
import tlc2.value.impl.BoolValue;

public class SymbolicSum extends SymbolicExpression {

    // INVARIANT: No two different keys are 'equal'
    private final Map<SymbolicExpression, Integer> bag = new HashMap<>();
    private int cardinality = 0;
    
    public SymbolicSum(final Map<SymbolicExpression, Integer> bag) {
        this.bag.putAll(bag);
        this.cardinality = bag.values().stream().mapToInt(Integer::intValue).sum();
    }

    protected Map<SymbolicExpression, Integer> getBag() {
        return this.bag;
    }

    protected int getCardinality() {
        return this.cardinality;
    }

    public SymbolicSum addTo(final SymbolicExpression e) {
        return addTo(e, 1);
    }

    public SymbolicSum addTo(final SymbolicExpression e, final int num) {
        try {
            final Map<SymbolicExpression, Integer> newBag = new HashMap<>(this.bag);
            newBag.put(e, newBag.getOrDefault(e, 0) + num);
            return new SymbolicSum(newBag);
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
            final SymbolicSum ret = new SymbolicSum(this.bag);
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

            /* Don't use FP64.exend for elements because it is not commutative */
            long h1 = 0L;
            long h2 = 0L;

            for (Map.Entry<SymbolicExpression, Integer> e : this.bag.entrySet()) {
                long k = e.getKey().fingerPrint(FP64.Zero);
                long v = (long) e.getValue();

                long x = mix64(k * 0x9E3779B97F4A7C15L ^ v * 0xC2B2AE3D27D4EB4FL);

                h1 += x;
                h2 ^= x;
            }

            fp = FP64.Extend(fp, mix64(h1 ^ h2));
            return FP64.Extend(fp, this.cardinality);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    // Strong 64-bit mixer (SplitMix64 finalizer)
    private static long mix64(long z) {
        z = (z ^ (z >>> 33)) * 0xff51afd7ed558ccdL;
        z = (z ^ (z >>> 33)) * 0xc4ceb9fe1a85ec53L;
        return z ^ (z >>> 33);
    }
}
