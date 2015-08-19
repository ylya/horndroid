package analysis;

public class DalvikImplementation {
	final private DalvikInstance di;
	final private DalvikMethod dm;
	public DalvikImplementation(final DalvikInstance di, final DalvikMethod dm){
		this.di = di;
		this.dm = dm;
	}
	public DalvikInstance getInstance(){
		return di;
	}
	public DalvikMethod getMethod(){
		return dm;
	}
}
