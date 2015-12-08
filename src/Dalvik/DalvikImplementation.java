package Dalvik;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

public class DalvikImplementation {
	final private DalvikClass dc;
	final private DalvikMethod dm;
	final private Set<DalvikInstance> di;
	
	public DalvikImplementation(final DalvikClass dc, final DalvikMethod dm){
		this.dc = dc;
		this.dm = dm;
		this.di = Collections.synchronizedSet(new HashSet<DalvikInstance>());
	}
	public DalvikClass getDalvikClass(){
		return dc;
	}
	public DalvikMethod getMethod(){
		return dm;
	}
	public void putInstance(final DalvikInstance di){
		this.di.add(di);
	}
	public Set<DalvikInstance> getInstances(){
		return di;
	}
}
