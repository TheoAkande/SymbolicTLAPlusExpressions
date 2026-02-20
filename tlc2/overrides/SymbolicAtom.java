package tlc2.overrides;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.IValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;
import tlc2.value.Values;

import util.Assert;

public class SymbolicAtom extends SymbolicExpression {

    private final String val;

    public static SymbolicAtom generate(final Value val) {
        final SymbolicAtom newAtom = new SymbolicAtom(val);
        final SymbolicExpression oldAtom = SymbolicExpression.get(newAtom);
        if (oldAtom != null) {
            return (SymbolicAtom) oldAtom;
        }
        newAtom.setup();
        return newAtom;
    } 

    // setup a new symbolic atom for le
    private void setup() {
        try {
            final Set<SymbolicExpression> le = this.getAllLE();
            final Set<SymbolicExpression> ge = this.getAllGE();
            le.add(SymbolicEmpty.getInstance());
            SymbolicEmpty.getInstance().setLessThan(this);
            le.add(this);
            ge.add(this);
            for (final SymbolicExpression greater : SymbolicExpression.ltRelation.getOrDefault(this, SymbolicExpression.emptySet)) {
                le.add(greater);
                le.addAll(greater.getAllGE());
                greater.setGreaterThan(this);
                for (final SymbolicExpression g: greater.getAllGE()) {
                    g.setGreaterThan(this);
                }
            }
            for (final SymbolicExpression lesser : SymbolicExpression.gtRelation.getOrDefault(this, SymbolicExpression.emptySet)) {
                ge.add(lesser);
                ge.addAll(lesser.getAllLE());
                lesser.setLessThan(this);
                for (final SymbolicExpression l: lesser.getAllLE()) {
                    l.setGreaterThan(this);
                }
            }
            SymbolicExpression.addExpression(this);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    // Private constructor to avoid making too many
    private SymbolicAtom(final Value val) {
        try {
            if (val instanceof StringValue) {
                this.val = ((StringValue) val).getVal().toString();
            } else {
                Assert.fail(
                    "Attempted to construct symbolic atom with non-string value " + Values.ppr(val.toString()),
                    getSource()
                );
                this.val = ""; // Keep compiler happy
            }
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    protected boolean isAtomExpr() {return true;}

    @Override
    public IValue deepCopy() {
        return new SymbolicAtom(new StringValue(val));
    }

    @Override
    public StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
        try {
            return sb.append(val);
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
            if (other instanceof SymbolicAtom) {
                ((SymbolicAtom)other).val.equals(this.val);
            }
            return false;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    protected long getFullFingerprint(long fp) {
        fp = FP64.Extend(fp, "SYMBOLICATOM");
        fp = FP64.Extend(fp, this.val.length());
        return FP64.Extend(fp, this.val.toString());
    }
}
