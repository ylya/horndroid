package analysis;

import org.jf.dexlib2.iface.instruction.Instruction;

import com.google.common.collect.ImmutableList;

public class DalvikMethod {
	final private String name;
	final private int numArg;
	final private int numReg;
	final private String returnType;
	final private boolean isVoid;
	final private ImmutableList<Instruction> instructions;
	DalvikMethod(final String name, final int numArg, final int numReg, final String returnType, final boolean isVoid, final ImmutableList<Instruction> instructions){
		this.name = name;
		this.numArg = numArg;
		this.numReg = numReg;
		this.returnType = returnType;
		this.isVoid = isVoid;
		this.instructions = instructions;
	}
	public String getName(){
		return name;
	}
	public int getNumArg(){
		return numArg;
	}
	public int getNumReg(){
		return numReg;
	}
	public String getReturnType(){
		return returnType;
	}
	public boolean isVoid(){
		return isVoid;
	}
	public ImmutableList<Instruction> getInstructions(){
		return instructions;
	}
}
