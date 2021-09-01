package justification;
import convertion.BackConverter;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.reasoner.NodeSet;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;
import javafx.beans.property.ObjectProperty;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.util.OWLEntityCollector;
import sun.reflect.generics.tree.ClassSignature;
import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.List;

public class expand {
    public expand(){

    }
    private OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
    public  boolean entailed(OWLReasoner reasoner, OWLAxiom i){

        System.out.println(i);
        if (i instanceof OWLSubObjectPropertyOfAxiom){
            OWLSubObjectPropertyOfAxiom now = (OWLSubObjectPropertyOfAxiom) i;
            OWLObjectPropertyExpression sub = now.getSubProperty();
            OWLObjectPropertyExpression sup = now.getSuperProperty();
            NodeSet<OWLObjectPropertyExpression> superList = reasoner.getSuperObjectProperties(sub,false);
            //System.out.println(superList+" "+sup);
            return superList.containsEntity(sup);
        }
        else if( i instanceof  OWLClassAxiom)return reasoner.isEntailed(i);
        else{
            System.out.print("this is unknown type ");

        }
        return true;
    }
    public Set<OWLAxiom> Expand(OWLOntology onto,OWLAxiom eta) throws Exception {

        System.out.println("module size:" +onto.getAxioms().size());
        Set<OWLAxiom> ans = new HashSet<>();
        OWLReasoner reasoner= new Reasoner(new Configuration(),onto);

        //OWLReasoner reasoner = new ElkReasonerFactory().createReasoner(onto);

        //OWLReasoner reasoner = new Reasoner.ReasonerFactory().createReasoner(onto);
        if(!entailed(reasoner,eta)){

            return ans;
        }
        Set<OWLAxiom> S1 = new HashSet<>();
        Set<OWLAxiom> S2 = new HashSet<>();
        Set<OWLClass> concepts = new HashSet<>(eta.getClassesInSignature());
        Set<OWLObjectProperty> roles = new HashSet<>(eta.getObjectPropertiesInSignature());
        do{
            S2 = new HashSet<>(S1);
            Set<OWLAxiom> newAxioms = GetDefiningAxioms(concepts,roles,onto);

            newAxioms.removeAll(S1);
            S1.addAll(newAxioms);
            reasoner= new Reasoner(new Configuration(),manager.createOntology(S1));


            if(entailed(reasoner,eta)){
                return S1;
            }
            concepts.addAll(getsignatureClass(S1));
            roles.addAll(getsignatureProperty(S1));
            System.out.print(1);
        }while(!equals(S1,S2));
        System.out.println();
        ans = onto.getAxioms();
        return  ans;
    }

    public Set<OWLAxiom> GetDefiningAxioms(Set<OWLClass> concepts, Set<OWLObjectProperty> roles, OWLOntology onto){
        Set<OWLAxiom> ans = new HashSet<>();
        for(OWLClass now : concepts){
            Set<OWLClassAxiom> temp = onto.getAxioms(now);
            ans.addAll(temp);
        }
        return ans;
    }

    public  boolean equals(Set<?> set1, Set<?> set2){
        if(set1 == null || set2 ==null){//null就直接不比了
            return false;
        }
        if(set1.size()!=set2.size()){//大小不同也不用比了
            return false;
        }
        return set1.containsAll(set2);//最后比containsAll
    }
    public Set<OWLClass> getsignatureClass(Set<OWLAxiom> S){
        Set<OWLClass> ans = new HashSet<>();
        for(OWLAxiom i :S){
            ans.addAll(i.getClassesInSignature());
        }
        return ans;
    }
    public Set<OWLObjectProperty> getsignatureProperty(Set<OWLAxiom> S){
        Set<OWLObjectProperty> ans = new HashSet<>();
        for(OWLAxiom i: S){
            ans.addAll(i.getObjectPropertiesInSignature());
        }
        return ans;
    }
/*
    public static Set<OWLEntity> getSignature(OWLAxiom axiom) {
        Set<OWLEntity> toReturn = new HashSet();
        OWLEntityCollector collector = new OWLEntityCollector(toReturn);
        collector.setCollectDatatypes(false);
        axiom.accept(collector);
        return toReturn;
    }

 */
    public static void main(String []args) throws Exception{

        String O2 = "/Users/liuzhao/nju/ontologyCompare/FINISHED/broEL/v3.2.1.owl";
        String implicitWitness = "/Users/liuzhao/nju/ontologyCompare/FINISHED/broEL/witness_implicit.owl";
        OWLOntology onto_2 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(O2));
        System.out.println(onto_2.getAxioms().size());
        OWLOntology onto_implicitWitness = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(implicitWitness));
        Set<OWLAxiom> axioms = onto_implicitWitness.getAxioms();
        long startTime1 = System.currentTimeMillis();
        for (OWLAxiom i : axioms) {
            Set<OWLAxiom> now = new expand().Expand(onto_2, i);
            OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
            contract Con = new contract();
            Set<OWLAxiom> fin = Con.Contract(now,i);
            System.out.println("fin size"+fin.size());
            System.out.println("eta:" +i);
            for(OWLAxiom j : fin){
                System.out.println(j);
            }
            OWLOntology track = manager.createOntology();
            for(OWLAxiom axiom : fin){
                manager.applyChange(new AddAxiom(track, axiom));
            }
            OWLReasoner reasoner2= new Reasoner(new Configuration(),track);

            if(reasoner2.isEntailed(i)){

                System.out.println("yes2");
            }
            else{
                System.out.println("no2");
            }
        }
        long endTime1 = System.currentTimeMillis();
        System.out.println("Total Duration = " + (endTime1 - startTime1)/100 + "millis");
    }
}
