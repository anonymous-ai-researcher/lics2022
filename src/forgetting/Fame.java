package forgetting;

import formula.Formula;
import roles.AtomicRole;
import concepts.AtomicConcept;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;

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
		
	public List<Formula> FameRC(Set<AtomicRole> r_sig, Set<AtomicConcept> c_sig, List<Formula> formula_list, OWLOntology onto) throws Exception {

		if (r_sig.isEmpty() && c_sig.isEmpty()) {
			return formula_list;
		}
				
		Forgetter ft = new Forgetter(); 

		List<Formula> forgetting_solution = ft.Forgetting(r_sig, c_sig, formula_list, onto);
		
	
		return forgetting_solution;
	}
	
}