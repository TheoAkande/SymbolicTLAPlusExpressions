package tlc2.overrides;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.IValue;
import tlc2.value.Values;
import util.Assert;

public class SymbolicMax extends SymbolicExpression {

    private final SymbolicExpression v1;
    private final SymbolicExpression v2;

    public static SymbolicMax generate(final IValue v1, final IValue v2) {
        final SymbolicMax newMax = new SymbolicMax(v1, v2);
        final SymbolicExpression oldMax = SymbolicExpression.get(newMax);
        if (oldMax != null) {
            return (SymbolicMax) oldMax;
        }
        newMax.setup();
        return newMax;
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
            for (final SymbolicExpression e : SymbolicExpression.getAll()) {
                if (v1.getAllLE().contains(e) || v2.getAllLE().contains(e)) {
                    le.add(e);
                    e.setLessThan(this);
                }
                if (v1.getAllGE().contains(e) && v2.getAllGE().contains(e)) {
                    ge.add(e);
                    e.setGreaterThan(this);
                } else if (v1.getAllGE().contains(e) || v2.getAllGE().contains(e)) {
                    // TODO: maybe try a comparison? - check if it is possible for this case to be resolved
                }
            }
            SymbolicExpression.addExpression(this);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    private SymbolicMax(final IValue v1, final IValue v2) {
        try {
            if (v1 instanceof SymbolicExpression && v2 instanceof SymbolicExpression) {
                final long f1 = v1.fingerPrint(FP64.Zero);
                final long f2 = v2.fingerPrint(FP64.Zero);
                this.v1 = (SymbolicExpression) (f1 < f2 ? v1 : v2);
                this.v2 = (SymbolicExpression) (f1 < f2 ? v2 : v1);
            } else {
                Assert.fail(
                    "Attempted to construct symbolic max with at least one non-symbolic expression " + Values.ppr(v1.toString())
                    + " or " + Values.ppr(v2.toString()),
                    getSource()
                );
                this.v1 = SymbolicEmpty.getInstance();
                this.v2 = SymbolicEmpty.getInstance();
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
        return new SymbolicMax(v1.deepCopy(), v2.deepCopy());
    }

    @Override
    public StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
        try {
            sb.append("Max(");
            v1.toString(sb, offset, swallow);
            sb.append(", ");
            v2.toString(sb, offset, swallow);
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
                return maxOther.v1.equals(this.v1) && maxOther.v2.equals(this.v2);
            }
            return false;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    protected long getFullFingerprint(long fp) {
        if (fp == FP64.Zero) {
            return this.getZeroFingerprint();
        }
        fp = FP64.Extend(fp, "MAX");
        fp = FP64.Extend(fp, v1.fingerPrint(FP64.Zero));
        return FP64.Extend(fp, v2.fingerPrint(FP64.Zero));
    }

    public SymbolicExpression first() {
        return v1;
    }

    public SymbolicExpression second() {
        return v2;
    }
}
