package tlc2.overrides;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.IValue;

public class SymbolicSum extends SymbolicExpression {
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
            if (s.cardinality == 0) {
                ret.add(SymbolicEmpty.getInstance());
            } else if (s.cardinality == 1) {
                ret.add((SymbolicExpression) s.bag.keySet().toArray()[0]);
            } else {
                ret.add(s);
            }
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

    // setup a new symbolic max for le
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
        final Set<SymbolicExpression> keys = this.bag.keySet();
        if (e.isEmptyExpr()) {
            return true;
        } else if (e.isAtomExpr()) {
            return this.atoms.contains(e);
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
        if (e.isEmptyExpr() || e.isAtomExpr()) {
            return false;
        }
        if (e.isMaxExpr()) {
            final SymbolicMax maxOther = (SymbolicMax) e;
            return this.lessThanWithoutCache(maxOther.first()) || this.lessThanWithoutCache(maxOther.second());
        }
        return ((SymbolicSum) e).greaterThanWithoutCache(this);
    }

    private boolean isOneGreater(final SymbolicExpression o) {
        if (o.isEmptyExpr()) return false;
        if (o.isAtomExpr() || o.isMaxExpr()) return this.cardinality == 2 && this.bag.containsKey(o);
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
