package analysis;

public class DalvikStaticField extends DalvikField {
	final private String defaultValue;
	DalvikStaticField(final String name, final String defaultValue){
		super(name);
		this.defaultValue = defaultValue;
	}
	public String getDefaultValue(){
		return defaultValue;
	}
}
