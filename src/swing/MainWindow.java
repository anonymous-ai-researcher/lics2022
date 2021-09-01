package swing;


import java.awt.Toolkit;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JScrollPane;

import concepts.AtomicConcept;
import formula.Formula;
import roles.AtomicRole;

public class MainWindow extends AbstractWindow {

	private static final long serialVersionUID = 1L;

	private JList<Formula> formula_list;
	private JList<AtomicRole> role_list;
	private JList<AtomicConcept> concept_list;
	private JList<Formula> result_list;
	private JButton btn_loading;
	private JButton btn_forgetting;
	private JButton btn_saving;

	protected void addListener() {
		btn_loading.addActionListener(new LoadButtonListener());
		btn_forgetting.addActionListener(new ForgetButtonListener());
		btn_saving.addActionListener(new SaveButtonListener());
	}

	protected void registerComponent() {
		Register.getInstance().registerObject("formula_list", formula_list);
		Register.getInstance().registerObject("role_list", role_list);
		Register.getInstance().registerObject("concept_list", concept_list);
		Register.getInstance().registerObject("result_list", result_list);
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	protected void init() {

		formula_list = new JList<Formula>(new SentenceListModel());
		JScrollPane scrollPane1 = new JScrollPane(formula_list);
		add(scrollPane1);
		
		role_list = new JList<AtomicRole>(new SentenceListModel());
		JScrollPane scrollPane2 = new JScrollPane(role_list);
		add(scrollPane2);

		concept_list = new JList<AtomicConcept>(new SentenceListModel());
		JScrollPane scrollPane3 = new JScrollPane(concept_list);
		add(scrollPane3);

		result_list = new JList<Formula>(new SentenceListModel());
		JScrollPane scrollPane4 = new JScrollPane(result_list);
		add(scrollPane4);

		scrollPane1.setBounds(0, 0, 250, 500);
		scrollPane2.setBounds(275, 0, 250, 245);
		scrollPane3.setBounds(275, 255, 250, 245);
		scrollPane4.setBounds(550, 0, 250, 500);

		btn_loading = new JButton("Load Ontology");
		btn_forgetting = new JButton("Forget");
		btn_saving = new JButton("Save Ontology");
				
		add(btn_loading);
		add(btn_forgetting);
		add(btn_saving);

		btn_loading.setBounds(50, 520, 150, 30);
		btn_forgetting.setBounds(325, 520, 150, 30);
		btn_saving.setBounds(600, 520, 150, 30);

		this.validate();
	}

	@Override
	protected void initWindow() {
		super.initWindow();
		setIconImage(Toolkit.getDefaultToolkit().getImage("src/logo.jpg"));
		setTitle("Forgetting and Uniform Interpolation for Expressive Description Logics");
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		setLayout(null);
	}

}
