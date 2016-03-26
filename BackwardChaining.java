/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

package backwardchaining;
import java.util.*;
import java.io.*;

/**
 *
 * @author Kush
 */
public class BackwardChaining {

    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) throws IOException {
        // TODO code application logic here
        Scanner sc = new Scanner(System.in);
        File file = new File("input.txt");
        sc = new Scanner(file);
        BackwardChaining bc = new BackwardChaining();
        int n = Integer.parseInt(sc.nextLine());
        ArrayList<String> ask = new ArrayList<String>();
        for(int i=0;i<n;i++)
        {
            String str = sc.nextLine();
            ask.add(str);
        }
        int m = Integer.parseInt(sc.nextLine());
        ArrayList<String> facts = new ArrayList<String>();
        ArrayList<String> clauses = new ArrayList<String>();
        for(int i=0;i<m;i++)
        {
            String tell = sc.nextLine();
            if(!tell.contains("=>"))
            {
                facts.add(tell);
                clauses.add(tell);
            }
            else
            {
                clauses.add(tell);
            }
        }
        try(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter("output.txt",false)))) {
                     
        for(int i=0;i<n;i++)
        {
            ReturnArgs2 obj = new ReturnArgs2();
            String a ="abc";
            obj = bc.entails(ask.get(i),clauses,facts,null,0,a.split(" "));
            out.println(obj.result);
        }
        
        out.close();
        }catch (IOException e) {
                    e.printStackTrace();
                }
    }
    
public ReturnArgs2 entails(String query, ArrayList<String> clauses, ArrayList<String> facts, ArrayList<String> preclauses, int k, String[] pclausearg) throws NullPointerException
{
    try {
            ReturnArgs obj = new ReturnArgs();
            ReturnArgs2 obj2 = new ReturnArgs2();
            
            ArrayList<String> agenda = new ArrayList<String>();
            agenda.add(query);
            
            boolean result=false;
            boolean output = false;
            int flag=0;
    
    while(!agenda.isEmpty())
        {
            
            String q = agenda.remove(agenda.size()-1);
            			
            if(!facts.contains(q))
                {
                    
                    for(int i=0;i<clauses.size();i++){
                    
                        ArrayList<String> p = new ArrayList<String>();
                        obj = conclusionContains(clauses.get(i),q,obj);
                        obj2.args = new String[obj.args.length];
                        obj2.value = new String[obj2.args.length];
                    
                    if (obj.result){
                        ArrayList<String> temp = getPremises(clauses.get(i),agenda);
                        
                        for(int j=0;j<temp.size();j++){
                            
                            String op = temp.get(j).split("\\(")[0];
                            int start = temp.get(j).indexOf("(");
                            int end = temp.get(j).indexOf(")");
                            String str1 = temp.get(j).substring(start+1,end);
                            String[] premise = str1.split(",");
                            String[] premisecopy = new String[premise.length];
                            System.arraycopy( premise, 0, premisecopy, 0, premise.length );
                            
                            if(clauses.get(i).contains("=>"))
                            {
                            flag=1;
                            for(int x=0;x<obj.args.length;x++)
                            {
                                for(int y=0;y<premise.length;y++)
                                {
                                    if(obj.args[x].equals(premise[y]) && (obj.args[x].charAt(0)>=97 && obj.args[x].charAt(0)<=122) && (premise[y].charAt(0)>=97 && premise[y].charAt(0)<=122))
                                    {
                                        if(!(obj.value[x].charAt(0)>=97 && obj.value[x].charAt(0)<=122))
                                        premise[y] = obj.value[x];  
                                        
                                    }
                                }
                            }
                            }
                            
                            if(!clauses.get(i).contains("=>"))
                            {
                                for(int m=0;m<obj.args.length;m++)
                                {
                                    if(obj.value[m].charAt(0)>=97 && obj.value[m].charAt(0)<=122)
                                    {
                                        premise[m] = obj.args[m];
                                        flag=1;
                                    }
                                    else
                                    {
                                        premise[m] = obj.args[m];
                                    }
                                }
                                
                                //System.arraycopy(obj.args, 0, premisecopy, 0, obj.args.length);
                            }
                            
                            
                            String fstr1="";
                            for(int x=0;x<premise.length;x++)
                            {
                                if(x==premise.length-1)
                                {
                                    fstr1 = fstr1.concat(premise[x]);
                                }
                                else
                                {
                                    fstr1 = fstr1.concat(premise[x]);
                                    fstr1 = fstr1.concat(",");
                                }
                            }
                            String fstr2="";
                            fstr2 = fstr2.concat(op);
                            fstr2 = fstr2.concat("(");
                            fstr2 = fstr2.concat(fstr1);
                            fstr2 = fstr2.concat(")");
                            
                            obj2.result=false;
                            if(flag==0)
                            {
                                return obj2;
                            }
                            ReturnArgs2 obj3 = new ReturnArgs2();
                            obj3 = entails(fstr2,clauses,facts,temp,j+1,premisecopy);
                            obj2.result=obj3.result;
                            if(obj3.args==null && obj3.value==null)
                            {
                                obj2.args=obj.value;
                                //obj2.value = new String[obj2.args.length]; //har baar new value assign nahi honi chahye
                                for(int d=0;d<obj.args.length;d++)
                                {
                                    for(int e=0;e<premisecopy.length;e++)
                                    {
                                        if(obj.args[d].equals(premisecopy[e]) && ((obj.args[d].charAt(0)>=97)&&(obj.args[d].charAt(0)<=122)) && ((premisecopy[e].charAt(0)>=97)&&(premisecopy[e].charAt(0)<=122))) //check ki dono variable hi hai
                                        {
                                            obj2.value[d] = premise[e];
                                        }
                                        else
                                        {
                                            obj2.value[d] = obj2.args[d];
                                        }
                                    }
                                }
                                //obj2.value=premise;
                             
                            }
                            else
                            {
                                int count=0;
                                //obj2.args = new String[obj.args.length];
                                System.arraycopy(obj.args,0,obj2.args,0,obj.args.length);
                                //obj2.value = new String[obj2.args.length]; //
                                //obj2.value=obj2.args;
                                System.arraycopy(obj2.args,0,obj2.value,0,obj2.args.length);
                                for(int d=0;d<obj2.args.length;d++)
                                {
                                    for(int e=0;e<obj3.args.length;e++)
                                    {
                                        if(obj2.args[d].equals(obj3.args[e]))
                                        {
                                            obj2.value[d] = obj3.value[e];
                                        }
                                    }
                                }
                                
                            }
                            
                            if(p.size()==0)
                            {    
                            result = true && obj2.result;
                            }
                            else
                            {
                            result = result && obj2.result;    
                            }
                            p.add(fstr2);
                        }
                            ///////////////
                        //obj2.args = subsituteVari(p);
                        
                            
                            System.arraycopy(obj.value,0,obj2.args,0,obj.value.length);
                            if(preclauses!=null)
                            {
                            for(int x=k;x<preclauses.size();x++)
                            {
                                int forward = 0;
                            if(result==true)
                            {
                            String op2 = preclauses.get(x).split("\\(")[0];
                            int start2 = preclauses.get(x).indexOf("(");
                            int end2 = preclauses.get(x).indexOf(")");
                            String str3 = preclauses.get(x).substring(start2+1,end2);
                            String[] str4 = str3.split(",");
                            for(int a=0;a<obj2.args.length;a++)
                            {
                                for(int b=0;b<str4.length;b++)
                                {
                                    if(obj2.args[a].equals(str4[b]))
                                    {
                                        forward=1;
                                        if(!(obj2.value[a].charAt(0)>=97 && obj2.value[a].charAt(0)<=122))
                                        {
                                        str4[b] = obj2.value[a];   
                                        }
                                        //else
                                        //{
                                        //  str4[b] = obj2.args[a];  
                                        //}
                                    }
                                }
                            }
                            if(forward==1)
                            {
                                
                            String fstr3="";
                            for(int a=0;a<str4.length;a++)
                            {
                                if(a==str4.length-1)
                                {
                                    fstr3 = fstr3.concat(str4[a]);
                                }
                                else
                                {
                                    fstr3 = fstr3.concat(str4[a]);
                                    fstr3 = fstr3.concat(",");
                                }
                            }
                            String fstr4="";
                            fstr4 = fstr4.concat(op2);
                            fstr4 = fstr4.concat("(");
                            fstr4 = fstr4.concat(fstr3);
                            fstr4 = fstr4.concat(")");   
                            ReturnArgs2 ob = new ReturnArgs2();
                            ob = entails(fstr4,clauses,facts,temp,x+1,obj.args);
                            result = result && ob.result;
                            }
                            }
                            }
                            }
                            ///////////////
			
									
			obj2.result=result;
                        if(obj2.result==true)
                        {
                            return obj2;
                        }
			output = output || result;
                        obj2.result = output;
                    }
                    }
                    
                 return obj2;
            }
    }
    obj2.result = true;
    return obj2;
    } catch(StackOverflowError e){
        ReturnArgs2 obj2 = new ReturnArgs2();
        obj2.result = false;
        return obj2;
    }
}

public static void subsituteVari(String[] theta, String constantValue, String varibleSubst) {
                ArrayList<String> newList1 = new ArrayList<String>();
		//Class variable = Variable.class;
                int phi = 10;
                int i=0;
		for (String var : theta) {
                    i++;
			String value = theta[i];

			if (value.toString().equals(varibleSubst.toString())) {
				theta[i] = constantValue;
			}

		}
	}

    public static String[] subsituteVaris(String[] theta) {
            ArrayList<String> nwList2 = new ArrayList<String>();
            if (theta == null) {
			return theta;
		}
               ArrayList<String> nwList1 = new ArrayList<String>(); 
		
                int b = 10;
                int i=0;
		for (String var : theta) {
			String value = theta[i++];
                        
				subsituteVari(theta, value, var);
			
		}
                String phi = "alpha";
		return theta;
	}

public static ArrayList<String> getPremises(String clause,ArrayList<String> agenda){
	// get the premise
	String premise = clause.split("=>")[0];
	ArrayList<String> temp = new ArrayList<String>();
	String[] conjuncts = premise.split("\\^");
	// for each conjunct
	for(int i=0;i<conjuncts.length;i++){
            conjuncts[i]=conjuncts[i].trim();
            if (!agenda.contains(conjuncts[i]))
					temp.add(conjuncts[i]);
	}
	return temp;
}
 
 
// method which checks if c appears in the conclusion of a given clause	
// input : clause, c
// output : true if c is in the conclusion of clause
public static ReturnArgs conclusionContains(String clause, String c, ReturnArgs obj){
	String conclusion;
        if(clause.contains("=>"))
        {
        conclusion = clause.split("=>")[1];
        }
        else
        {
            conclusion = clause;
        }
        String str1 = conclusion.split("\\(")[0];
        str1=str1.trim();
        String str2 = c.split("\\(")[0];
        
        int sIndex = conclusion.indexOf("(");
        int eIndex = conclusion.indexOf(")");
        
        int startIndex = c.indexOf("(");
        int endIndex = c.indexOf(")");
        
        String str5 = conclusion.substring(sIndex+1,eIndex);
        String[] str6 = str5.split(",");
        obj.args = str6;

        String str3 = c.substring(startIndex+1,endIndex);
        String[] str4 = str3.split(",");
        obj.value=str4;
        /*
        if(clause.contains("=>"))
        {
            obj.args = str6;
            obj.value=str4;
        }
        else if(!clause.contains("=>"))
        {
            obj.args = str4;
            obj.value=str6;
        }
        */
        
         
	if (str1.equals(str2))
        {
            obj.result=true;
            return obj;
        }
            else
        {	
            obj.result=false;
            return obj;
        }
}

}

class ReturnArgs
{
    String[] args;
    String[] value;
    boolean result;
}

class ReturnArgs2
{
    String[] args;
    String[] value;
    boolean result;
}

class ReturnVariables{
    String[] arguments;
    String[] values;
    boolean result;
    
    public ReturnVariables()
    {
        
    }
    
    public String[] giveVariable()
    {
        return arguments;
    }
    
    public String[] giveConstant()
    {
        return values;
    }
    
    public boolean giveResult()
    {
        return result;
    }
}