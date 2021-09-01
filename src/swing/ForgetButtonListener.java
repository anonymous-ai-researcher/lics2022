package swing;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import javax.swing.JList;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.IRIDocumentSource;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyLoaderConfiguration;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import concepts.AtomicConcept;
import convertion.Converter;
import forgetting.Fame;
import formula.Formula;
import roles.AtomicRole;

public class ForgetButtonListener implements ActionListener {
	
	private JList<AtomicRole> Jrole_list;
	private JList<AtomicConcept> Jconcept_list;
	// private JList<Formula> Jformula_list;
	private JList<Formula> Jresult_list;

	@SuppressWarnings("unchecked")
	public ForgetButtonListener() {
		Jrole_list = (JList<AtomicRole>) Register.getInstance().getObject("role_list");
		Jconcept_list = (JList<AtomicConcept>) Register.getInstance().getObject("concept_list");
		// Jformula_list = (JList<Formula>) R.getInstance().getObject("formula_list");
		Jresult_list = (JList<Formula>) Register.getInstance().getObject("result_list");
	}

	@SuppressWarnings({ "rawtypes", "unchecked" })
	public void actionPerformed(ActionEvent arg0) {
		
		int indices_1[] = Jrole_list.getSelectedIndices();

		int indices_2[] = Jconcept_list.getSelectedIndices();
		
		SentenceListModel role_model = (SentenceListModel) Jrole_list.getModel();

		SentenceListModel concept_model = (SentenceListModel) Jconcept_list.getModel();

		List<AtomicRole> role_list = role_model.getListData();
		
		List<AtomicConcept> concept_list = concept_model.getListData();

		// SentenceListModel formula_model = (SentenceListModel)
		// Jformula_list.getModel();

		// List<Formula> formula_list = formula_model.getListData();

		SentenceListModel result_model = (SentenceListModel) Jresult_list.getModel();

		List<Formula> result_list = result_model.getListData();

		Set<AtomicRole> r_sig = new HashSet<>();

		int i = indices_1.length;

		while (i-- > 0) {
			r_sig.add(role_list.get(indices_1[i]));
		}
		
		Set<AtomicConcept> c_sig = new HashSet<>();

		int j = indices_2.length;

		while (j-- > 0) {
			c_sig.add(concept_list.get(indices_2[j]));
		}

		Fame fame = new Fame();

		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();

		IRI iri = IRI.create(new File(LoadButtonListener.ontologyPath));

		OWLOntology ontology = null;
		List<Formula> formula_list = null;

		Converter ct = new Converter();

		try {
			long startTime = System.currentTimeMillis();
			ontology = manager.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri),
					new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(true));
			formula_list = ct.OntologyConverter(ontology);
			result_list = fame.FameRC(r_sig, c_sig, formula_list, ontology);
			long endTime = System.currentTimeMillis();
			System.out.println("Duration = " + (endTime - startTime) + "millis");
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		result_model.setListData(result_list);
	}

}
