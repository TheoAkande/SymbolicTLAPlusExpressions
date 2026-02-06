package tlc2.overrides;

import java.util.HashMap;
import java.util.Map;

import tlc2.tool.FingerprintException;
import tlc2.value.IValue;
import tlc2.util.FP64;

public class SymbolicEmpty extends SymbolicExpression {

    @Override
    protected boolean isEmptyExpr() {return true;}

    @Override
    public IValue deepCopy() {
        return this;
    }

    @Override
    public StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
        try {
            return sb.append("EMPTY");
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }

    @Override
    protected Map<SymbolicExpression, Integer> getValue() {
        return new HashMap<>();
    }
    
    @Override
    public boolean equals(final Object other) {
        try {
            if (other instanceof SymbolicEmpty) {
                return true;
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
            return FP64.Extend(fp, "EMPTY");
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {throw FingerprintException.getNewHead(this, e);}
            else {throw e;}
        }
    }
}
