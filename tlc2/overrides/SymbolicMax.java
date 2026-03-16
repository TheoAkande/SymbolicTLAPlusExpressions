package tlc2.overrides;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.IValue;
import tlc2.value.Values;
import util.Assert;

public class SymbolicMax extends SymbolicExpression {

    protected final Set<SymbolicExpression> vs = new HashSet<>();
    private final List<SymbolicExpression> orderedVs = new ArrayList<>();

    public static SymbolicMax generate(final IValue v1, final IValue v2) {
        final SymbolicExpression s1 = (SymbolicExpression) v1;
        final SymbolicExpression s2 = (SymbolicExpression) v2;

        if (s1.isMaxExpr() && s2.isMaxExpr()) {
            SymbolicMax newMax = (SymbolicMax) s1;
            for (final SymbolicExpression e : ((SymbolicMax) s2).vs) {
                newMax = newMax.with(e);
            }
            return newMax;
        } else if (s1.isMaxExpr()) {
            return ((SymbolicMax) s1).with(s2);
        } else if (s2.isMaxExpr()) {
            return ((SymbolicMax) s2).with(s1);
        }
        final SymbolicMax newMax = new SymbolicMax(v1, v2);
        final SymbolicExpression oldMax = SymbolicExpression.get(newMax);
        if (oldMax != null) {
            return (SymbolicMax) oldMax;
        }
        try {
            SymbolicExpression.acquireGenerationLock();
            if (SymbolicExpression.get(newMax) != null) {
                return (SymbolicMax) SymbolicExpression.get(newMax);
            }
            newMax.setup();
            return newMax;
        } finally {
            SymbolicExpression.releaseGenerationLock();
        }
    }

    protected SymbolicMax with(final SymbolicExpression n) {
        if (this.vs.contains(n)) {
            return this;
        }
        final Set<SymbolicExpression> newVs = new HashSet<>();
        for (final SymbolicExpression e : this.vs) {
            if (SymbolicExpression.le(n, e) == UNKNOWN) { // We know that n is not < e, but it might be > e
                newVs.add(e);
            }
        }
        newVs.add(n);
        final SymbolicMax other = new SymbolicMax();
        other.vs.addAll(newVs);
        final long nfp = n.getZeroFingerprint();
        boolean inserted = false;
        for (final SymbolicExpression e : this.orderedVs) {
            if (!inserted && nfp < e.getZeroFingerprint()) {
                other.orderedVs.add(n);
                inserted = true;
            }
            if (newVs.contains(e)) {
                other.orderedVs.add(e);
            }
        }
        if (!inserted) {
            other.orderedVs.add(n);
        }
        final SymbolicExpression oldMax = SymbolicExpression.get(other);
        if (oldMax != null) {
            return (SymbolicMax) oldMax;
        }
        try {
            SymbolicExpression.acquireGenerationLock();
            if (SymbolicExpression.get(other) != null) {
                return (SymbolicMax) SymbolicExpression.get(other);
            }
            other.setup();
            return other;
        } finally {
            SymbolicExpression.releaseGenerationLock();
        }
    }

    @Override
    protected void setup() {
        try {
            for (final SymbolicExpression e : this.vs) {
                this.atoms.addAll(e.atoms);
            }
            SymbolicExpression.addExpression(this);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    private SymbolicMax() {}

    private SymbolicMax(final IValue v1, final IValue v2) {
        try {
            if (v1 instanceof SymbolicExpression && v2 instanceof SymbolicExpression) {
                final long f1 = v1.fingerPrint(FP64.Zero);
                final long f2 = v2.fingerPrint(FP64.Zero);
                this.vs.add((SymbolicExpression) v1);
                this.vs.add((SymbolicExpression) v2);
                if (f1 < f2) {
                    this.orderedVs.add((SymbolicExpression) v1);
                    this.orderedVs.add((SymbolicExpression) v2);
                } else {
                    this.orderedVs.add((SymbolicExpression) v2);
                    this.orderedVs.add((SymbolicExpression) v1);
                }
            } else {
                Assert.fail(
                    "Attempted to construct symbolic max with at least one non-symbolic expression " + Values.ppr(v1.toString())
                    + " or " + Values.ppr(v2.toString()),
                    getSource()
                );
            }
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    protected boolean isMaxExpr() {return true;}

    @Override
    public IValue deepCopy() {
        return this;
    }

    @Override
    public StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
        try {
            sb.append("Max(");
            sb.append(this.orderedVs.stream().map(Object::toString).collect(Collectors.joining(", ")));
            return sb.append(")");
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    protected Map<SymbolicExpression, Integer> getValue() {
        try {
            final Map<SymbolicExpression, Integer> v =  new HashMap<>();
            v.put(this, 1);
            return v;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }
    
    @Override
    public boolean equals(final Object other) {
        try {
            if (other instanceof SymbolicMax) {
                final SymbolicMax maxOther = (SymbolicMax) other;
                if (this.orderedVs.size() != maxOther.orderedVs.size()) {
                    return false;
                }
                for (int i = 0; i < this.orderedVs.size(); i++) {
                    if (!this.orderedVs.get(i).equals(maxOther.orderedVs.get(i))) {
                        return false;
                    }
                }
                return true;
            }
            return false;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    protected long getFullFingerprint(long fp) {
        fp = FP64.Extend(fp, "MAX");
        for (final SymbolicExpression e : this.orderedVs) {
            fp = FP64.Extend(fp, e.fingerPrint(FP64.Zero));
        }
        return fp;
    }
}
