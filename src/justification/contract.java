package justification;

import org.apache.commons.lang3.ObjectUtils;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import com.google.common.collect.Sets;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class contract {
    public contract(){

    }
    private OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
    public Set<OWLAxiom> Contract(Set<OWLAxiom> axioms,OWLAxiom eta) throws Exception{

        return ContractAxiomsRecursive(new HashSet<>(),axioms,eta);

    }
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
    public Set<OWLAxiom> ContractAxiomsRecursive(Set<OWLAxiom> S_support,Set<OWLAxiom> S_whole, OWLAxiom eta) throws Exception{
        if(S_whole.size() == 1) return S_whole;
        List<OWLAxiom> listAxioms = new ArrayList<>(S_whole);
        List<OWLAxiom>tempSl = new ArrayList<>(listAxioms.subList(0,S_whole.size()/2));
        List<OWLAxiom>tempSr = new ArrayList<>(listAxioms.subList(S_whole.size()/2,S_whole.size()));
        Set<OWLAxiom> SL = new HashSet<>(tempSl);
        Set<OWLAxiom> SR = new HashSet<>(tempSr);
        OWLReasoner reasoner= new Reasoner(new Configuration(),manager.createOntology(Sets.union(SL,S_support)));

        //OWLReasoner reasoner = new ElkReasonerFactory().createReasoner(manager.createOntology(Sets.union(SL,S_support)));
        if(entailed(reasoner,eta)){
            return ContractAxiomsRecursive(S_support,SL,eta);
        }
        reasoner= new Reasoner(new Configuration(),manager.createOntology(Sets.union(SR,S_support)));
        //reasoner =new ElkReasonerFactory().createReasoner(manager.createOntology(Sets.union(SR,S_support)));
        if(entailed(reasoner,eta)){
            return ContractAxiomsRecursive(S_support,SR,eta);
        }
        Set<OWLAxiom> SLTemp = ContractAxiomsRecursive( Sets.union(SR,S_support),SL,eta);
        Set<OWLAxiom> SRTemp = ContractAxiomsRecursive( Sets.union(SLTemp,S_support),SR,eta);

        return Sets.union(SLTemp,SRTemp);
    }
}
