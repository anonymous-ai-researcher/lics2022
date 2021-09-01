package swing;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.Collections;
import java.util.List;

import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JList;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.IRIDocumentSource;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyLoaderConfiguration;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import concepts.AtomicConcept;
import convertion.Converter;
import formula.Formula;
import roles.AtomicRole;

public class LoadButtonListener implements ActionListener {
	
	
	public OWLOntology ontology = null;

	public void setontology(OWLOntology onto) {
		ontology = onto;
	}
 
     public OWLOntology getontology() {  
       return ontology;  
   }  

	private JList<Formula> formula_list;
	private JList<AtomicRole> role_list;
	private JList<AtomicConcept> concept_list;
	private JList<AtomicConcept> result_list;
	public static String ontologyPath = "";

	@SuppressWarnings("unchecked")
	public LoadButtonListener() {
		formula_list = (JList<Formula>) Register.getInstance().getObject("formula_list");
		role_list = (JList<AtomicRole>) Register.getInstance().getObject("role_list");
		concept_list = (JList<AtomicConcept>) Register.getInstance().getObject("concept_list");
		result_list = (JList<AtomicConcept>) Register.getInstance().getObject("result_list");
	}

	@SuppressWarnings({ "rawtypes", "unchecked" })
	public void actionPerformed(ActionEvent arg0) {

		JFileChooser jfc = new JFileChooser();
		jfc.setFileSelectionMode(JFileChooser.FILES_AND_DIRECTORIES);
		int returnVal = jfc.showDialog(new JLabel(), "Select an Ontology");
		if (returnVal == JFileChooser.APPROVE_OPTION) {
			List<Formula> formulaList = null;
			List<AtomicRole> roleList = null;
			List<AtomicConcept> conceptList = null;
			
			
			SentenceListModel formula_model = null;
			if(formula_list.getModel().getSize() != 0){
				formula_model = (SentenceListModel) formula_list.getModel();
				formula_model.removeAllElements();
				formula_model.notifyDataChanged();
			}
			SentenceListModel role_model = null;
			if(role_list.getModel().getSize() != 0){
				int[] indexs = {};
				role_list.setSelectedIndices(indexs);
				role_model = (SentenceListModel) role_list.getModel();
				role_model.removeAllElements();
				role_model.notifyDataChanged();
			}
			SentenceListModel concept_model = null;
			if(concept_list.getModel().getSize() != 0){
				int[] indexs = {};
				concept_list.setSelectedIndices(indexs);
				concept_model = (SentenceListModel) concept_list.getModel();
				concept_model.removeAllElements();
				concept_model.notifyDataChanged();
			}
			if(result_list.getModel().getSize() != 0){
				SentenceListModel result_model = (SentenceListModel) result_list.getModel();
				result_model.removeAllElements();
				result_model.notifyDataChanged();
			}
			File file = jfc.getSelectedFile();
			ontologyPath = file.getAbsolutePath();
			OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
			IRI iri = IRI.create(file);
			
			Converter ct = new Converter();
			//BackConverter bc = new BackConverter();
			//PreProcessor pp = new PreProcessor();
			try {
				ontology = manager.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri),
						new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(true));
				System.out.println("===================================================");
				System.out.println("Ontology Metrics:");
				System.out.println("No. of Logical Axioms: " + ontology.getLogicalAxiomCount());
				System.out.println("No. of Concept Names: " + ontology.getClassesInSignature().size());
				System.out.println("No. of Role Names: " + ontology.getObjectPropertiesInSignature().size());
				System.out.println("No. of Individuals: " + ontology.getIndividualsInSignature().size());
				System.out.println("===================================================");
				//formulaList = bc.toAxiomsList(pp.getCNF(pp.getSimplifiedForm(pp.getClauses(ct.OntologyConverter_ShortForm(ontology)))));
				formulaList = ct.OntologyConverter(ontology);
				roleList = ct.getRolesInSignature(ontology);
				conceptList = ct.getConceptsInSignature(ontology);
				Collections.sort(roleList);
				Collections.sort(conceptList);
			} catch (OWLOntologyCreationException e2) {
				// TODO Auto-generated catch block
				e2.printStackTrace();
			}
			formula_model = (SentenceListModel)formula_list.getModel();
			formula_model.setListData(formulaList);
			role_model = (SentenceListModel)role_list.getModel();
			role_model.setListData(roleList);
			concept_model = (SentenceListModel)concept_list.getModel();
			concept_model.setListData(conceptList);
		}
	}

}
