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
        SymbolicSum base =  SymbolicSum.generate(new HashMap<>());
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

    private static Set<SymbolicExpression> flatten(final Map<SymbolicExpression, Integer> bag) {
        final Set<SymbolicSum> flat = new HashSet<>();
        SymbolicSum baseWithAtoms =  SymbolicSum.generate(new HashMap<>());
        for (final Map.Entry<SymbolicExpression, Integer> e : bag.entrySet()) {
            if (e.getKey().isAtomExpr()) {
                baseWithAtoms = baseWithAtoms.addTo(e.getKey(), e.getValue());
            }
        }
        for (final Map.Entry<SymbolicExpression, Integer> e : bag.entrySet()) {
            if (e.getKey().isAtomExpr()) {
                continue;
            }
            assert e.getKey().isMaxExpr(); // It has to be a max expression
            flat.add(SymbolicSum.combine(baseWithAtoms, ((SymbolicMax) e.getKey()).first(), e.getValue()));
            flat.add(SymbolicSum.combine(baseWithAtoms, ((SymbolicMax) e.getKey()).second(), e.getValue()));
        }
        if (flat.isEmpty()) {
            flat.add(baseWithAtoms);
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
        newSum.setup();
        return newSum;
    } 

    // setup a new symbolic sum for le
    private void setup() {
        try {
            for (final SymbolicExpression e : this.bag.keySet()) {
                this.atoms.addAll(e.atoms);
            }
            final Set<SymbolicExpression> le = this.getAllLE();
            final Set<SymbolicExpression> ge = this.getAllGE();
            le.add(SymbolicEmpty.getInstance());
            SymbolicEmpty.getInstance().setLessThan(this);
            le.add(this);
            ge.add(this);
            SymbolicExpression.addExpression(this); // TODO: Check that this doesn't cause recursive failures
            for (final SymbolicExpression e : SymbolicExpression.getAll()) {
                if (this.greaterThanWithoutCache(e)) {
                    le.add(e);
                    e.setLessThan(this);
                } else if (this.lessThanWithoutCache(e)) {
                    ge.add(e);
                    e.setGreaterThan(this);
                }
            }
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
        if (this.equals(e)) {
            return false;
        }
        final Set<SymbolicExpression> keys = this.bag.keySet();
        if (e.isEmptyExpr()) {
            return true;
        } else if (e.isAtomExpr()) {
            return this.atoms.contains(e);
        } else if (e.isMaxExpr()) {
            final SymbolicMax m = (SymbolicMax) e;
            return (this.equals(m.first()) || this.greaterThanWithoutCache(m.first())) && (this.equals(m.second()) || this.greaterThanWithoutCache(m.second()));
        } else if (e.isSumExpr()) {
            final SymbolicSum other = (SymbolicSum) e;
            final Set<SymbolicExpression> otherKeys = other.bag.keySet();
            final Map<SymbolicExpression, Integer> thisWithoutCommon = new HashMap<>();
            final Map<SymbolicExpression, Integer> otherWithoutCommon = new HashMap<>();

            for (final SymbolicExpression exp : keys) {
                final int expV = this.bag.get(exp) - other.bag.getOrDefault(exp, 0);
                if (expV > 0) {
                    thisWithoutCommon.put(exp, expV);
                } else if (expV < 0) {
                    otherWithoutCommon.put(exp, -expV);
                }
            }
            for (final SymbolicExpression exp : otherKeys) {
                if (keys.contains(exp)) {
                    continue;
                }
                final int expV = other.bag.get(exp) - this.bag.getOrDefault(exp, 0);
                if (expV > 0) {
                    otherWithoutCommon.put(exp, expV);
                } else if (expV < 0) {
                    thisWithoutCommon.put(exp, -expV);
                }
            }

            final Set<SymbolicExpression> thisFlat = SymbolicSum.flatten(thisWithoutCommon);
            final Set<SymbolicExpression> otherFlat = SymbolicSum.flatten(otherWithoutCommon);

            for (final SymbolicExpression thisExp : thisFlat) {
                boolean geAll = true;
                for (final SymbolicExpression otherExp : otherFlat) {
                    if (!geAll || !SymbolicExpression.le(otherExp, thisExp)) {
                        geAll = false;
                        break;
                    }
                }
                if (geAll) {
                    return true;
                }
            }
        }
        return false;
    }

    private boolean lessThanWithoutCache(final SymbolicExpression e) {
        if (this.equals(e)) {
            return false;
        }
        if (e.isEmptyExpr() || e.isAtomExpr()) {
            return false;
        }
        if (e.isMaxExpr()) {
            final SymbolicMax maxOther = (SymbolicMax) e;
            return this.lessThanWithoutCache(maxOther.first()) || this.lessThanWithoutCache(maxOther.second());
        }
        return ((SymbolicSum) e).greaterThanWithoutCache(this);
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
            sb.append(" : (" + this.cardinality + ")");
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
