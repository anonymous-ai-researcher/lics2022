package justification;

import org.semanticweb.owlapi.model.OWLAxiom;
import convertion.BackConverter;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;
import javafx.beans.property.ObjectProperty;
import org.apache.commons.lang3.builder.ToStringExclude;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.util.OWLEntityCollector;
import sun.reflect.generics.tree.ClassSignature;
import java.io.File;
import java.util.*;

public class HintTree {
    public class node{
        Set<OWLAxiom> just;
        Set<OWLAxiom> path;
        public node(){
            just = new HashSet<>();
            path = new HashSet<>();
        }
        public node(Set<OWLAxiom> j){
            just = j;
            path = new HashSet<>();
        }
        public node(Set<OWLAxiom> j,Set<OWLAxiom> p){
            just = j;
            path = p;
        }

    }
    private OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
    public HintTree(){

    }
    OWLOntology computeModule(OWLOntology originalOnto,OWLAxiom eta) throws Exception{
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager, originalOnto, ModuleType.STAR);
        Set<OWLAxiom> moduleAxioms = extractor.extract(eta.getSignature());
        return manager.createOntology(moduleAxioms);
    }
    public Set<Set<OWLAxiom>> ComputeAllJust(OWLOntology onto,OWLAxiom eta) throws Exception{
        Set<Set<OWLAxiom>> ans = new HashSet<>();
        OneJustification oj = new OneJustification();
        OWLOntology module = computeModule(onto,eta);
        Set<OWLAxiom> S_working = module.getAxioms();
        Set<Set<OWLAxiom>> X_explored = new HashSet<>();
        Set<Set<OWLAxiom>> X_result = new HashSet<>();
        Set<OWLAxiom> J_root = oj.computeOneJust(module,eta);
        X_result.add(J_root);
        Queue<node> Q = new LinkedList<>();
        node T_root = new node(J_root);
        Q.offer(T_root);
        while(Q.size() != 0){
            node J_head = Q.poll();
            for(OWLAxiom axioms : J_head.just){
                Set<OWLAxiom> S_path = new HashSet<>();
                S_path.addAll(J_head.path);
                S_path.add(axioms);
                if(!X_explored.contains(S_path)){
                    X_explored.add(S_path);
                    Set<OWLAxiom> J_now = GetNonIntersectingJust(S_path,X_result);
                    if(J_now.size() == 0){
                        S_working.removeAll(S_path);
                        J_now =  oj.computeOneJust(manager.createOntology(S_working),eta);
                        S_working.addAll(S_path);
                    }
                    if(J_now.size() != 0){
                        X_result.add(J_now);
                        Q.offer(new node(J_now,S_path));
                    }

                }
            }
        }
        return X_result;
    }
    public Set<OWLAxiom> GetNonIntersectingJust(Set<OWLAxiom> S_path,
                                                Set<Set<OWLAxiom>> X_result){
        Set<OWLAxiom> ans = new HashSet<>();

        for(Set<OWLAxiom> setAxioms : X_result){
            ans.clear();
            ans.addAll(setAxioms);
            ans.retainAll(S_path);
            if(ans.size() != 0){
                return setAxioms;
            }
        }
        return ans;
    }
    public static  void main(String []args) throws  Exception{
        HintTree tree = new HintTree();
        String O2 = "/Users/liuzhao/nju/ontologyCompare/FINISHED/broEL/v3.2.1.owl";
        String implicitWitness = "/Users/liuzhao/nju/ontologyCompare/FINISHED/broEL/witness_implicit.owl";
        OWLOntology onto_2 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(O2));
        System.out.println(onto_2.getAxioms().size());
        OWLOntology onto_implicitWitness = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(implicitWitness));
        Set<OWLAxiom> axioms = onto_implicitWitness.getAxioms();
        long startTime1 = System.currentTimeMillis();
        for(OWLAxiom axiom : axioms){
            Set<Set<OWLAxiom>> just = tree.ComputeAllJust(onto_2,axiom);
            System.out.println("just num:"+just.size());
            int num = 0;
            for(Set<OWLAxiom> n : just){
                System.out.println(num+" size "+n.size());
                for(OWLAxiom i : n){
                    System.out.println(i);
                }
                num++;
            }
        }
    }


}
