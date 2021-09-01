package BackTrack;

import concepts.AtomicConcept;
import connectives.And;
import connectives.Exists;
import connectives.Inclusion;
import convertion.BackConverter;
import forgetting.LDiff;
import formula.Formula;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import roles.AtomicRole;
import java.util.*;

public   class BackTrack {
    public static int HashCode = 1;
    public static HashMap<Integer,Set<Integer>> FatherHash = new HashMap<>();
    public static HashMap<Formula,Integer > Formula2Int = new HashMap<>();
    public static HashMap<Integer,Formula> Int2Formula = new HashMap<>();

    public static void addFatherHash(Formula child, Formula Father1,int tag) throws  Exception{
        //System.out.println("behind :"+child+" "+Father1+" "+tag);


        Set<Integer> thisFather = new LinkedHashSet<>();
        int childHashcode;
        if(Formula2Int.containsKey(child)){
            childHashcode = Formula2Int.get(child);
        }
        else{
            childHashcode = HashCode;
            Formula2Int.put(child,HashCode);
            Int2Formula.put(HashCode,child);
            HashCode++;
        }
        if(FatherHash.containsKey(childHashcode)){
            thisFather = FatherHash.get(childHashcode);
        }
        int num = thisFather.size();
        if(Formula2Int.containsKey(Father1)){
            thisFather.add(Formula2Int.get(Father1));

        }
        else{
            Formula2Int.put(Father1,HashCode);
            Int2Formula.put(HashCode,Father1);
            thisFather.add(HashCode);
            HashCode++;
        }

        FatherHash.put(childHashcode,thisFather);
        if(thisFather.contains(childHashcode)){
            System.out.println("Back Track circle "+ "original size: "+num +" type :"+tag);
            System.out.println("child :");
            System.out.println(Int2Formula.get(childHashcode));
            System.out.println("  father :"+Father1+" ");

            System.out.println("father :");
            for (Integer i : thisFather){
                System.out.print(" "+ Int2Formula.get(i)+" ");

            }
            thisFather.remove(childHashcode);

            System.out.println();
            //throw new Exception("Back Track circle");
        }

    }

    public static void addFatherHash(Formula child, Formula Father1, Formula Father2,int tag) throws  Exception{
        //System.out.println("behind :"+child+" "+Father1+" "+Father2+" "+tag);
        //System.out.println("behind HashCode:"+child.hashCode()+" "+Father1.hashCode()+" "+Father2.hashCode()+" ");
        //System.out.println("behind clone HashCode:"+child.clone().hashCode()+" "+Father1.clone().hashCode()+" "+Father2.clone().hashCode()+" ");

        //System.out.println("Int2Formula1 :"+Formula2Int.get(child)+" "+Formula2Int.get(Father1)+" "+Formula2Int.get(Father2));

        Set<Integer> thisFather = new LinkedHashSet<>();
        Set<Formula> Father = new LinkedHashSet<>();
        Father.add(Father1.clone());
        Father.add(Father2.clone());
        int childHashcode;
        if(Formula2Int.containsKey(child)){
            childHashcode = Formula2Int.get(child);
        }
        else{
            childHashcode = HashCode;
            Formula2Int.put(child,HashCode);
            Int2Formula.put(HashCode,child);
            HashCode++;
        }
        if(FatherHash.containsKey(childHashcode)){
            thisFather = FatherHash.get(childHashcode);
        }
        int num = thisFather.size();
        for(Formula axiom : Father){
            if(Formula2Int.containsKey(axiom)){

                thisFather.add(Formula2Int.get(axiom));

            }
            else{
                Formula2Int.put(axiom,HashCode);
                Int2Formula.put(HashCode,axiom);
                thisFather.add(HashCode);
                HashCode++;
            }
        }
        FatherHash.put(childHashcode,thisFather);
        //System.out.println("Int2Formula2 :"+Formula2Int.get(child)+" "+Formula2Int.get(Father1)+" "+Formula2Int.get(Father2));
        if(thisFather.contains(childHashcode)){

            System.out.println("Back Track circle2 "+ "original size: "+num +" type :"+tag);
            System.out.println("child :");
            System.out.println(Int2Formula.get(childHashcode));
            System.out.println("  father1 :"+Father1+" "+"  father2 "+ Father2);
            System.out.println("father :");
            for (Integer i : thisFather){
                System.out.print(" "+ Int2Formula.get(i)+" ");
            }
            System.out.println();
            thisFather.remove(childHashcode);

            //throw new Exception("Back Track circle");
        }
    }

    public static void getInferencePath(Formula child){
        if(Formula2Int.get(child) == null){
            System.out.println("NullPointerException :");
            return;
        }
        int childHashCode =  Formula2Int.get(child);
        ArrayList<Integer> Queue = new ArrayList<>();
        Queue.add(childHashCode);
        while(Queue.size()!= 0){
            int len  = Queue.size();
            while(len > 0){
                int nowHashCode = Queue.get(0);
                Queue.remove(0);
                len--;
                System.out.print("  child :  "+Int2Formula.get(nowHashCode) +"  father : ");
                for(Integer i : FatherHash.get(nowHashCode)){
                    System.out.print(Int2Formula.get(i)+"  ");
                    if(FatherHash.get(i) != null){
                        Queue.add(i);
                    }
                    else{
                        System.out.print("    ***null(in the original Ontology)***    ");
                    }
                }
                System.out.println();
            }

        }


    }
    public static void main(String [] args) throws Exception{
        /*
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        BackConverter bc = new BackConverter();
        AtomicConcept a1 = new AtomicConcept("A");
        AtomicConcept b1 = new AtomicConcept("B");
        AtomicConcept c1 = new AtomicConcept("C");
        AtomicConcept d1 = new AtomicConcept("D");

        Inclusion inc1 = new Inclusion(a1, b1);
        Inclusion inc2 = new Inclusion(b1, c1);
        Inclusion inc3 = new Inclusion(c1, d1);
        OWLAxiom temp1 = bc.toOWLAxiom(inc1);
        OWLAxiom temp2 = bc.toOWLAxiom(inc2);
        OWLAxiom temp3 = bc.toOWLAxiom(inc3);
        OWLOntology onto2 = manager.createOntology();
        manager.applyChange(new AddAxiom(onto2, temp1));
        manager.applyChange(new AddAxiom(onto2, temp2));
        manager.applyChange(new AddAxiom(onto2, temp3));

        Inclusion inc4 = new Inclusion(a1, d1);
        OWLAxiom temp4 = bc.toOWLAxiom(inc4);
        OWLOntology onto1 = manager.createOntology();
        manager.applyChange(new AddAxiom(onto1, temp4));
        LDiff ldiff = new LDiff();
        ldiff.compute_LDiff(onto1,onto2,"/Users/liuzhao/Desktop");
        getInferencePath(temp4);

         */
        Set<Character>now = new LinkedHashSet<>();
        now.add('2');
        now.add('1');
        now.add('g');
        now.add('l');
        for(int i = 0; i < 100 ; i++){
            for(Character j : now){
                System.out.print(j+" ");
            }
            System.out.println();
        }
        Set<Character>now1 = new LinkedHashSet<>();
        now1.add('2');
        now1.add('1');
        now1.add('8');
        now1.add('l');
        for(int i = 0; i < 100 ; i++){
            for(Character j : now1){
                System.out.print(j+" ");
            }
            System.out.println();
        }
    }
}
