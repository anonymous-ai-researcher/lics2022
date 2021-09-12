package forgetting;

import convertion.BackConverter;
import convertion.Converter;
import formula.Formula;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import roles.AtomicRole;
import concepts.AtomicConcept;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import java.util.HashSet;
import java.util.List;
import java.util.Set;


/**
 *
 * @author Yizheng
 */
public class Fame {

	public static OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	
	public Fame() {

	}
		
	public List<Formula> FameRC(Set<AtomicRole> r_sig, Set<AtomicConcept> c_sig, OWLOntology onto) throws Exception {

		if (r_sig.isEmpty() && c_sig.isEmpty()) {
			return new Converter().OntologyConverter(onto);
		}
				
		Forgetter ft = new Forgetter();
		BackConverter bc = new BackConverter();
		Set<OWLObjectProperty> roles = new HashSet<>();
		for(AtomicRole r : r_sig){
			roles.add(bc.toOWLObjectProperty(r));
		}
		Set<OWLClass> concepts = new HashSet<>();
		for(AtomicConcept c : c_sig){
			concepts.add(bc.toOWLClass(c));
		}
		List<Formula> forgetting_solution = ft.Forgetting(roles, concepts, onto,new saveMetrics());
		
	
		return forgetting_solution;
	}
	
}