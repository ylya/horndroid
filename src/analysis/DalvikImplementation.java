package analysis;

import java.util.Collections;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

public class DalvikImplementation {
	final private DalvikClass dc;
	final private DalvikMethod dm;
	final private Set<DalvikInstance> di;
	public DalvikImplementation(final DalvikClass dc, final DalvikMethod dm){
		this.dc = dc;
		this.dm = dm;
		this.di = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<DalvikInstance, Boolean>()));
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
