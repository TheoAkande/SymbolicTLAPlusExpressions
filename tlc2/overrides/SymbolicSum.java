package tlc2.overrides;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.IValue;
import tlc2.value.impl.BoolValue;

public class SymbolicSum extends SymbolicExpression {

    // INVARIANT: No two different keys are 'equal'
    private final Map<SymbolicExpression, Integer> bag = new HashMap<>();
    private int cardinality = 0;
    
    // Note: addTo is generally better to use (hence private)
    private static SymbolicSum generate(final Map<SymbolicExpression, Integer> bag) {
        final SymbolicSum newSum = new SymbolicSum(bag);
        final SymbolicExpression oldSum = SymbolicExpression.get(newSum);
        if (oldSum != null) {
            return (SymbolicSum) oldSum;
        }
        newSum.setup();
        return newSum;
    } 

    // setup a new symbolic max for le
    private void setup() {
        try {
            final Set<SymbolicExpression> le = this.getAllLE();
            final Set<SymbolicExpression> ge = this.getAllGE();
            le.add(SymbolicEmpty.getInstance());
            SymbolicEmpty.getInstance().setLessThan(this);
            le.add(this);
            ge.add(this);
            final Set<SymbolicExpression> keys = this.bag.keySet();
            for (final SymbolicExpression e : SymbolicExpression.getAll()) {
                if (this.greaterThanWithoutCache(e)) {
                    le.add(e);
                    e.setLessThan(this);
                } else if (this.lessThanWithoutCache(e)) {
                    ge.add(e);
                    e.setGreaterThan(this);
                }
            }
            SymbolicExpression.addExpression(this);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    private SymbolicSum(final Map<SymbolicExpression, Integer> bag) {
        this.bag.putAll(bag);
        this.cardinality = bag.values().stream().mapToInt(Integer::intValue).sum();
    }

    private boolean greaterThanWithoutCache(final SymbolicExpression e) {
        final Set<SymbolicExpression> keys = this.bag.keySet();
        if (e.isEmpty()) {
            return true;
        } else if (e.isAtom()) {
            for (final SymbolicExpression o : keys) {
                if (o.getAllLE().contains(e)) {
                    return true;
                }
            }
        } else if (e.isMaxExpr()) {
            final SymbolicMax m = (SymbolicMax) e;
            return this.greaterThanWithoutCache(m.first()) && this.greaterThanWithoutCache(m.second());
        } else if (e.isSumExpr()) {
            // A sum should always be one more than an existing sum (known to be less); if not then this wont be known either
            for (final SymbolicExpression o : e.getAllGE()) {
                if (this.isOneGreater(o)) {
                    return true;
                }
            }
            // TODO: What if its not one more than an existing sum? How do i handle this waaaaaa
        }
        return false;
    }

    private boolean lessThanWithoutCache(final SymbolicExpression e) {
        // TODO: Finish
        return false;
    }

    private boolean isOneGreater(final SymbolicExpression o) {
        if (o.isEmpty()) return false;
        if (o.isAtom() || o.isMaxExpr()) return this.cardinality == 2 && this.bag.containsKey(o);
        if (o.isSumExpr()) {
            final SymbolicSum sumOther = (SymbolicSum) o;
            if (sumOther.cardinality != this.cardinality - 1) {
                return false;
            }
            boolean oneDifference = false;
            for (final SymbolicExpression v : this.bag.keySet()) {
                if (!sumOther.bag.containsKey(v)) {
                    if (oneDifference || this.bag.get(v) > 1) {
                        return false;
                    }
                    oneDifference = true;
                } else {
                    if (sumOther.bag.get(v) != this.bag.get(v)) {
                        if (oneDifference) {
                            return false;
                        }
                        oneDifference = true;
                    }
                }
            }
            return oneDifference;
        }
        return false;
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
            return SymbolicSum.generate(newBag);
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
            final SymbolicSum ret = SymbolicSum.generate(this.bag);
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
                if (sumOther.cardinality != this.cardinality) {
                    return false;
                }
                return this.bag.equals(sumOther.bag);
            }
            return false;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    protected long getFullFingerprint(long fp) {
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
    }

    // Strong 64-bit mixer (SplitMix64 finalizer)
    private static long mix64(long z) {
        z = (z ^ (z >>> 33)) * 0xff51afd7ed558ccdL;
        z = (z ^ (z >>> 33)) * 0xc4ceb9fe1a85ec53L;
        return z ^ (z >>> 33);
    }
}
