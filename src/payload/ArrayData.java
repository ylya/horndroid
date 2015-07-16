package payload;

import java.util.List;

public class ArrayData {
	final int c, m, codeAddress;
	final List<Number> elements;
	public ArrayData(final int c, final int m, final int codeAddress, final List<Number> elements){
		this.c = c;
		this.m = m;
		this.codeAddress = codeAddress;
		this.elements = elements;
	}
	public List<Number> getElements(final int c, final int m, final int codeAddress){
		if ((this.c == c) && (this.m == m) && (this.codeAddress == codeAddress)){
			return elements;
		}
		return null;
	}
}
