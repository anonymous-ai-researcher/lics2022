package swing;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.List;

import javax.swing.JFileChooser;
import javax.swing.JList;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.OWLXMLOntologyFormat;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import convertion.BackConverter;
import formula.Formula;

public class SaveButtonListener implements ActionListener {
	private JList<Formula> j_result_list;

	@SuppressWarnings("unchecked")
	public SaveButtonListener() {
		j_result_list = (JList<Formula>) Register.getInstance().getObject("result_list");
	}

	private SimpleDateFormat sdf = new SimpleDateFormat("yyyyMMddHHmmss");

	@Override
	@SuppressWarnings({ "rawtypes", "unchecked" })
	public void actionPerformed(ActionEvent actionEvent) {
		SentenceListModel result_model = (SentenceListModel) j_result_list.getModel();
		List<Formula> result_list = result_model.getListData();
		BackConverter bc = new BackConverter();
		try {
			JFileChooser chooser = new JFileChooser();
			chooser.setFileSelectionMode(JFileChooser.FILES_AND_DIRECTORIES);
			int returnVal = chooser.showOpenDialog(null);
			if (returnVal == JFileChooser.APPROVE_OPTION) {
				//System.err.println(chooser.getSelectedFile().isDirectory());
				File file = null;
				if (chooser.getSelectedFile().isDirectory()) {
					String path = chooser.getSelectedFile().getPath();
					Date date = new Date(System.currentTimeMillis());
					String nowTime = sdf.format(date);
					file = new File(path + "\\ontology" + nowTime + ".owl");
				} else {
					String path = chooser.getSelectedFile().getPath();
					file = new File(path);
				}
				OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
				OutputStream os = new FileOutputStream(file);
				OWLOntology ontology = bc.toOWLOntology(result_list);
				manager.saveOntology(ontology, new OWLXMLOntologyFormat(), os);

			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

}
