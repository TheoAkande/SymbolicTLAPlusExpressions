package tlc2.overrides;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.IValue;

public class SymbolicSum extends SymbolicExpression {

    // 0 -> common, 1 -> just s1, 2 -> just s2
    protected static SymbolicSum[] split(final SymbolicSum s1, final SymbolicSum s2) {
        SymbolicSum base = SymbolicSum.generate(new HashMap<>());
        SymbolicSum justS1 = SymbolicSum.generate(new HashMap<>());
        SymbolicSum justS2 = SymbolicSum.generate(new HashMap<>());
        
        for (final SymbolicExpression e : s1.bag.keySet()) {
            if (s2.bag.containsKey(e)) {
                final int v1 = s1.bag.get(e);
                final int v2 = s2.bag.get(e);
                base = base.addTo(e, Math.min(v1, v2));
                if (v1 > v2) {
                    justS1 = justS1.addTo(e, v1 - v2);
                } else if (v2 > v1) {
                    justS2 = justS2.addTo(e, v2 - v1);
                }
            } else {
                justS1 = justS1.addTo(e, s1.bag.get(e));
            }
        }
        for (final SymbolicExpression e : s2.bag.keySet()) {
            if (!s1.bag.containsKey(e)) {
                justS2 = justS2.addTo(e, s2.bag.get(e));
            }
        }

        return new SymbolicSum[]{base, justS1, justS2};
    }

    private static SymbolicSum combine(final SymbolicSum base, final SymbolicExpression other, final int mult) {
        if (other.isEmptyExpr()) {
            return base;
        }
        if (other.isAtomExpr() || other.isMaxExpr()) {
            return base.addTo(other, mult);
        }
        SymbolicSum ret = base;
        final SymbolicSum sumOther = (SymbolicSum) other;
        for (final Map.Entry<SymbolicExpression, Integer> e : sumOther.bag.entrySet()) {
            ret = ret.addTo(e.getKey(), mult * e.getValue());
        }
        return ret;
    }

    private SymbolicSum extractAtoms() {
        SymbolicSum baseWithAtoms =  SymbolicSum.generate(new HashMap<>());
        for (final Map.Entry<SymbolicExpression, Integer> e : this.bag.entrySet()) {
            if (e.getKey().isAtomExpr()) {
                baseWithAtoms = baseWithAtoms.addTo(e.getKey(), e.getValue());
            }
        }
        return baseWithAtoms;
    }

    protected Set<SymbolicExpression> flatten() {
        final SymbolicSum baseWithAtoms = this.extractAtoms();
        Set<SymbolicSum> flat = new HashSet<>();
        flat.add(baseWithAtoms);
        for (final Map.Entry<SymbolicExpression, Integer> e : bag.entrySet()) {
            if (e.getKey().isAtomExpr()) {
                continue;
            }
            assert e.getKey().isMaxExpr(); // It has to be a max expression
            final Set<SymbolicSum> newFlat = new HashSet<>();
            for (final SymbolicSum s : flat) {
                for (final SymbolicExpression me : ((SymbolicMax) e.getKey()).vs) {
                    newFlat.add(SymbolicSum.combine(s, me, e.getValue()));
                }
            }
            flat = newFlat;
        }
        final Set<SymbolicExpression> ret = new HashSet<>();
        for (final SymbolicSum s : flat) {
            ret.add(s.extract());
        }

        return ret;
    }

    // INVARIANT: No two different keys are 'equal'
    private final Map<SymbolicExpression, Integer> bag = new HashMap<>();
    private int cardinality = 0;
    
    // Note: addTo is generally better to use (hence private)
    protected static SymbolicSum generate(final Map<SymbolicExpression, Integer> bag) {
        final SymbolicSum newSum = new SymbolicSum(bag);
        final SymbolicExpression oldSum = SymbolicExpression.get(newSum);
        if (oldSum != null) {
            return (SymbolicSum) oldSum;
        }
        try {
            SymbolicExpression.acquireGenerationLock();
            if (SymbolicExpression.get(newSum) != null) {
                return (SymbolicSum) SymbolicExpression.get(newSum);
            }
            newSum.setup();
            return newSum;
        } finally {
            SymbolicExpression.releaseGenerationLock();
        }
    } 

    @Override
    protected void setup() {
        try {
            for (final SymbolicExpression e : this.bag.keySet()) {
                this.atoms.addAll(e.atoms);
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

    protected SymbolicExpression extract() {
        if (this.cardinality == 0) {
            return SymbolicEmpty.getInstance();
        }
        if (this.cardinality == 1) {
            return (SymbolicExpression) this.bag.keySet().toArray()[0];
        }
        return this;
    }

    protected Map<SymbolicExpression, Integer> getBag() {
        return this.bag;
    }

    protected int getCardinality() {
        return this.cardinality;
    }

    public SymbolicSum addTo(final SymbolicExpression e) {
        try {
            final Map<SymbolicExpression, Integer> newBag = new HashMap<>(this.bag);
            newBag.put(e, newBag.getOrDefault(e, 0) + 1);
            return SymbolicSum.generate(newBag);
        } catch (final RuntimeException | OutOfMemoryError err) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, err);}
            else {throw err;}
        }
    }

    public SymbolicSum addTo(final SymbolicExpression e, final int num) {
        SymbolicSum exp = this;
        for (int i = 0; i < num; i++) {
            exp = exp.addTo(e);
        }
        return exp;
    }

    @Override
    protected boolean isSumExpr() {return true;}

    @Override
    public IValue deepCopy() {
        try {
            return this;
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
