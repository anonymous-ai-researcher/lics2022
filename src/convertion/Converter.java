/*
1 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package convertion;

import concepts.AtomicConcept;
import concepts.TopConcept;
import connectives.And;
import connectives.Equivalence;
import connectives.Exists;
import connectives.Inclusion;
import formula.Formula;
import roles.AtomicRole;
import roles.RoleExpression;
import roles.TopRole;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.*;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;



/**
 *
 * @author Yizheng
 */
public class Converter {
		
	public AtomicConcept getConceptfromClass(OWLEntity owlClass) {
		return new AtomicConcept(owlClass.getIRI().toString());
	}

	public AtomicRole getRoleFromObjectProperty(OWLEntity owlObjectProperty) {		
		return new AtomicRole(owlObjectProperty.getIRI().toString());
	}
	
	public Set<AtomicConcept> getConceptsfromClasses(Set<OWLClass> class_set) {

		Set<AtomicConcept> concept_set = new LinkedHashSet<>();

		for (OWLClass owlClass : class_set) {
			concept_set.add(getConceptfromClass(owlClass));
		}

		return concept_set;
	}

	public Set<AtomicRole> getRolesfromObjectProperties(Set<OWLObjectProperty> op_set) {

		Set<AtomicRole> role_set = new LinkedHashSet<>();

		for (OWLObjectProperty owlObjectProperty : op_set) {
			role_set.add(getRoleFromObjectProperty(owlObjectProperty));
		}

		return role_set;
	}
				
	public List<AtomicConcept> getConceptsInSignature(OWLOntology ontology) {

		List<AtomicConcept> concept_list = new ArrayList<>();
		Set<OWLClass> class_set = ontology.getClassesInSignature();

		for (OWLClass owlClass : class_set) {
			concept_list.add(getConceptfromClass(owlClass));
		}

		return concept_list;
	}
		
	public List<AtomicRole> getRolesInSignature(OWLOntology ontology) {

		List<AtomicRole> role_list = new ArrayList<>();
		Set<OWLObjectProperty> op_set = ontology.getObjectPropertiesInSignature();

		for (OWLObjectProperty owlObjectProperty : op_set) {
			role_list.add(getRoleFromObjectProperty(owlObjectProperty));
		}
		return role_list;
	}
	public List<Formula> RightSubformulasConverter(List<Formula> formulaList){
		List<Formula> ans = new ArrayList<>();
		for(Formula formula : formulaList){
			ans.add(RightSubformulaConverter(formula));
		}
		return ans;
	}
	public Formula RightSubformulaConverter(Formula formula){
		if(formula instanceof AtomicConcept || formula instanceof AtomicRole){
			return formula;
		}
		else if(formula instanceof Inclusion){
			return new Inclusion(RightSubformulaConverter(formula.getSubFormulas().get(0)),
					RightSubformulaConverter(formula.getSubFormulas().get(1)));
		}
		else if(formula instanceof Exists){
			return new Exists(formula.getSubFormulas().get(0),RightSubformulaConverter(formula.getSubFormulas().get(1)));
		}
		else if(formula instanceof And){
			Set<Formula> and = new LinkedHashSet<>();
			for(Formula f: formula.getSubformulae()){
				if(f instanceof And){
					for(Formula i:f.getSubformulae()){
						and.add(RightSubformulaConverter(i));
					}
				}
				else{
					and.add(RightSubformulaConverter(f));
				}
			}
			return  And.getAnd(and);
		}
		else{
			return formula;
		}
	}
	public List<Formula> OntologyConverter(OWLOntology ontology) {

		List<Formula> formula_list = new ArrayList<>();		
		Set<OWLLogicalAxiom> owlAxiom_set = ontology.getLogicalAxioms();
		
		long startTime1 = System.currentTimeMillis();
		
		for (OWLAxiom owlAxiom : owlAxiom_set) {
			List<Formula> temp_list = AxiomConverter(owlAxiom);
			temp_list = RightSubformulasConverter(temp_list);
			for (Formula formula : temp_list) {
				Formula subsumer = formula.getSubFormulas().get(1);
				if (subsumer instanceof And) {
					Formula subsumee = formula.getSubFormulas().get(0);
					Set<Formula> conjunct_set = subsumer.getSubformulae();

					for (Formula conjunct : conjunct_set) {
						//if(conjunct == null) {System.out.println("iiiiii");System.out.println(subsumer);}
						Formula inclusion = new Inclusion(subsumee, conjunct);
						formula_list.add(inclusion);
					}
					
				} else {
					formula_list.add(formula);
				}
			}
			//formula_list.addAll(temp_list);
		}
		
		long endTime1 = System.currentTimeMillis();
		
		System.out.println("Convertion Duration = " + (endTime1 - startTime1) + " millis");
		return formula_list;
	}
	public List<Formula> AxiomConverter_rightAnd(OWLAxiom owlAxiom){
		if(owlAxiom instanceof OWLEquivalentClassesAxiom){
			OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) owlAxiom;
			Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlECA.asOWLSubClassOfAxioms();
			List<Formula> converted = new ArrayList<>();
			Formula f1 = null, f2 =null;
			for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
				f1 = ClassExpressionConverter(owlSCOA.getSubClass());
				f2 = ClassExpressionConverter(owlSCOA.getSuperClass());
				break;
				//converted.addAll(AxiomConverter(owlSCOA));
			}
			if(f1 == null || f2 == null) return  Collections.emptyList();
			Formula temp = new Equivalence(f1,f2);
			converted.add(temp);

			return converted;
		}else{
			List<Formula> temp_list = AxiomConverter(owlAxiom);
			temp_list = RightSubformulasConverter(temp_list);
			return temp_list;
		}

	}
	public List<Formula> AxiomConverter_rightAnd(Set<OWLLogicalAxiom> set){
		List<Formula> temp_list = new ArrayList<>();
		for(OWLAxiom axiom : set){
			temp_list.addAll(AxiomConverter_rightAnd(axiom));
		}
		return temp_list;
	}
	
	public List<Formula> AxiomsConverter(Set<OWLLogicalAxiom> owlAxiom_set) {

		List<Formula> formula_list = new ArrayList<>();
		
		long startTime1 = System.currentTimeMillis();

		for (OWLAxiom owlAxiom : owlAxiom_set) {
			List<Formula> temp_list = AxiomConverter(owlAxiom);
			temp_list = RightSubformulasConverter(temp_list);
			//右边and拆开
			for (Formula formula : temp_list) {
				Formula subsumer = formula.getSubFormulas().get(1);
				if (subsumer instanceof And) {
					//System.out.println("formula = " + formula);
					Formula subsumee = formula.getSubFormulas().get(0);
					Set<Formula> conjunct_set = subsumer.getSubformulae();
					for (Formula conjunct : conjunct_set) {
						if(conjunct == null) System.out.println("jjjjj");

						Formula inclusion = new Inclusion(subsumee, conjunct);
						formula_list.add(inclusion);
					}
					
				} else {
					formula_list.add(formula);
				}
			}
		}
		
		long endTime1 = System.currentTimeMillis();
		
	//	System.out.println("Convertion Duration = " + (endTime1 - startTime1) + " millis");

		return formula_list;
	}
	
	
	/*public List<Formula> AxiomsConverter(Set<OWLAxiom> owlAxiom_set) {

		List<Formula> formula_list = new ArrayList<>();

		for (OWLAxiom owlAxiom : owlAxiom_set) {
			formula_list.addAll(AxiomConverter(owlAxiom));
		}

		return formula_list;
	}*/


		
	private List<Formula> AxiomConverter(OWLAxiom axiom) {
		if (axiom instanceof OWLSubClassOfAxiom) {
			OWLSubClassOfAxiom owlSCOA = (OWLSubClassOfAxiom) axiom;
			Formula l = ClassExpressionConverter(owlSCOA.getSubClass());
			Formula r = ClassExpressionConverter(owlSCOA.getSuperClass());
			if(l == null || r == null) return  Collections.emptyList();
			Formula converted = new Inclusion(l, r);
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLEquivalentClassesAxiom) {
			OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
			Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlECA.asOWLSubClassOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
				List<Formula> temp = AxiomConverter(owlSCOA);
				if(temp.size() == 0) return Collections.emptyList();
				converted.addAll(temp);
			}

			return converted;

		}  else if (axiom instanceof OWLObjectPropertyDomainAxiom) {
			OWLObjectPropertyDomainAxiom owlOPDA = (OWLObjectPropertyDomainAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlOPDA.asOWLSubClassOfAxiom();
			return AxiomConverter(owlSCOA);

		} else if (axiom instanceof OWLObjectPropertyRangeAxiom) {
			OWLObjectPropertyRangeAxiom owlOPRA = (OWLObjectPropertyRangeAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlOPRA.asOWLSubClassOfAxiom();
			return AxiomConverter(owlSCOA);

		} else if (axiom instanceof OWLSubObjectPropertyOfAxiom) {
			OWLSubObjectPropertyOfAxiom owlSOPOA = (OWLSubObjectPropertyOfAxiom) axiom;
			Formula l = RoleExpressionConverter(owlSOPOA.getSubProperty());
			Formula r = RoleExpressionConverter(owlSOPOA.getSuperProperty());
			if(l == null || r == null) return Collections.emptyList();
			Formula converted = new Inclusion(l, r);
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLEquivalentObjectPropertiesAxiom) {
			OWLEquivalentObjectPropertiesAxiom owlEOPA = (OWLEquivalentObjectPropertiesAxiom) axiom;
			Collection<OWLSubObjectPropertyOfAxiom> owlSOPOAs = owlEOPA.asSubObjectPropertyOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubObjectPropertyOfAxiom owlSOPOA : owlSOPOAs) {
				converted.addAll(AxiomConverter(owlSOPOA));
			}

			return converted;
			
		} 

		return Collections.emptyList();
	}


	public Formula ClassExpressionConverter(OWLClassExpression concept) {
	
		if (concept.isTopEntity()) {
			return TopConcept.getInstance();

		} else if (concept instanceof OWLClass) {
			OWLClass owlClass = (OWLClass) concept;
			return new AtomicConcept(owlClass.getIRI().toString());

		} else if (concept instanceof OWLObjectSomeValuesFrom) {
			OWLObjectSomeValuesFrom owlOSVF = (OWLObjectSomeValuesFrom) concept;
			RoleExpression r = RoleExpressionConverter(owlOSVF.getProperty());
			Formula c = ClassExpressionConverter(owlOSVF.getFiller());
			if(r == null || c == null) return null;
			return new Exists(r,c);

		} else if (concept instanceof OWLObjectIntersectionOf) {
			OWLObjectIntersectionOf owlOIO = (OWLObjectIntersectionOf) concept;
			Set<Formula> conjunct_set = new LinkedHashSet<>();
			for (OWLClassExpression conjunct : owlOIO.getOperands()) {

				Formula temp = ClassExpressionConverter(conjunct);
				if(temp == null) return null;

				conjunct_set.add(temp);

			}
			return  And.getAnd(conjunct_set);

		} 
		return null;
		//return TopConcept.getInstance();
	}
	
	private RoleExpression RoleExpressionConverter(OWLObjectPropertyExpression role) {

		if (role instanceof OWLObjectProperty) {
			OWLObjectProperty owlOP = (OWLObjectProperty) role;
			return new AtomicRole(owlOP.getIRI().toString());
			
		}
		return null;
		//return TopRole.getInstance();
	}
	

	public static  void main(String [] args){

		Set<Formula> now = new LinkedHashSet<>();
		Set<Formula> now2 =new LinkedHashSet<>();
		now2.add(new AtomicConcept("A"));
		now2.add(new AtomicConcept("B"));
		Formula and =  And.getAnd(now2);
		Set<Formula> temp = new HashSet<>();
		temp.add(and);
		temp.add(new AtomicConcept("H"));
		now.add(new Exists(new AtomicRole("r"), And.getAnd(temp)));
		now.add(new AtomicConcept("C"));
		System.out.println(now);

		Formula temp2 = new Converter().RightSubformulaConverter( And.getAnd(now));
		System.out.println(temp2);
		System.out.println(temp2.getSubformulae());
		for(Formula t : temp2.getSubformulae()){
			if(t instanceof Exists){
				System.out.println(t.getSubFormulas().get(1).getSubformulae());
			}
		}
	}

}
