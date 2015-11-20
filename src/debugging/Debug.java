package debugging;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.util.HashMap;

import org.jf.dexlib2.iface.instruction.Instruction;

import analysis.Analysis;
import analysis.DalvikMethod;

public class Debug {
    private Analysis analysis;
    private HashMap<String,HashMap<String,MethodeInfo>> debug = new HashMap<>();

    public Debug(Analysis analysis){
        this.analysis = analysis;
    }
    
    public MethodeInfo get(String c,String m){
        if (debug.containsKey(c)){
          if(debug.get(c).containsKey(m)){
              return debug.get(c).get(m);
          }else{
              DalvikMethod dm = analysis.getExactMethod(c.hashCode(), m.hashCode());
              int numReg = dm.getNumReg() + 1;
              int numPC = analysis.getImplementations(c.hashCode(), m.hashCode()).size();
              MethodeInfo mi = new MethodeInfo(analysis,c,m,numReg,numPC);
              debug.get(c).put(m, mi);
              return mi;
          }
        }else{
            debug.put(c, new HashMap<String,MethodeInfo>());
            DalvikMethod dm = analysis.getExactMethod(c.hashCode(), m.hashCode());
            int numReg = dm.getNumReg() + 1;
            int numPC = analysis.getImplementations(c.hashCode(), m.hashCode()).size();
            MethodeInfo mi = new MethodeInfo(analysis,c,m,numReg,numPC);
            debug.get(c).put(m, mi);
            return mi;
        }
    }
    
    private void tabular(final PrintWriter writer,int length){
        writer.println("");
        writer.print("\\begin{tabular}{|l|");
        for (int i = 0; i < length; i++){
            writer.print("c|");
        }
        writer.print("}\n");
        writer.println("\\hline");
    }
    
    private void item(final PrintWriter writer, final boolean bool){
        if (bool)
            writer.print("$\\cbullet$");
        else
            writer.print("$\\times$");
    }
    
    private void tripleline(final PrintWriter writer,final RegInfo reginf, final String linestring){
        writer.print("\\multirow{3}{*}{" + linestring + "} ");
        for (int i : reginf.high.keySet()){
            writer.print(" & ");
            item(writer,reginf.high.get(i));
        }
        writer.print("\\\\ \\cline{2-" + (reginf.high.size()+ 1) + "}\n");
        for (int i : reginf.local.keySet()){
            writer.print(" & ");
            item(writer,reginf.local.get(i));
        }
        writer.print("\\\\ \\cline{2-" + (reginf.local.size() + 1) + "}\n");
        for (int i : reginf.global.keySet()){
            writer.print(" & ");
            item(writer,reginf.global.get(i));
        }
        writer.print("\\\\ \\hline");
    }
    
    private void newcm(final PrintWriter writer, final String c, final String m){
        writer.print("\\begin{verbatim}\n" + c + " " + m + "\n\\end{verbatim}\n\n");
        DalvikMethod dc = analysis.getExactMethod(c.hashCode(), m.hashCode());
        if (dc == null)
            return;
        writer.println("\\begin{itemize}");
        for (final Instruction inst : dc.getInstructions()){
            writer.print("\\item $" + inst.getOpcode().toString().replaceAll("_", "\\\\;\\\\;") + "$\n");
        }
        writer.println("\\end{itemize}");
    }
    
    
    public void printToLatex(){
        try{
            final PrintWriter writer = new PrintWriter("./debug.tex", "UTF-8");
            for (String c : debug.keySet()){
                for (String m : debug.get(c).keySet()){
                    final MethodeInfo minfo = debug.get(c).get(m);
                    this.newcm(writer,c,m);
                    
                    /*tabular(writer,minfo.regInfo[0].high.size());
                    int length = minfo.regInfo.length;
                    writer.print(" $ $");
                    for (int i : minfo.regInfo[0].global.keySet()){
                        writer.print(" & $" + i + "$ ");
                    }
                    writer.println("\\\\ \\hline");
                    
                    for (int i = 0; i < length - 1;i++){
                        tripleline(writer,minfo.regInfo[i],"" + i);
                        writer.print("\n");
                    }
                    writer.print("\\end{tabular}\n\n\n");*/
                    
                    tabular(writer,minfo.regInfo[0].high.size());
                    int length = minfo.getLHKeySet().size();
                    writer.print(" $ $");
                    for (int i : minfo.regInfo[0].global.keySet()){
                        writer.print(" & $" + i + "$ ");
                    }
                    writer.println("\\\\ \\hline");
                    
                    for (final LHKey lhkey : minfo.getLHKeySet()){
                        final LHInfo lhinfo = minfo.getLHInfo(lhkey);
                        tripleline(writer,lhinfo.regInfo,
                                "\\begin{tabular}{c}\n" + lhinfo.allocatedClass + "\\\\ \n"+ lhinfo.c + "\\\\ \n" + lhinfo.m + "\\\\ \n" + lhinfo.pc + " " + lhinfo.field + "\n\\end{tabular}\n"
                                );
                        writer.print("\n");
                    }
                    writer.print("\\end{tabular}\n\n\n"); 
                }
            }
            writer.close();
        } catch (FileNotFoundException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (UnsupportedEncodingException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

    }
    
}
