package convertion;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.*;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.EntityType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;

import concepts.AtomicConcept;
import concepts.BottomConcept;
import concepts.TopConcept;
import connectives.And;
import connectives.Exists;
import connectives.Inclusion;
import formula.Formula;
import individual.Individual;
import roles.AtomicRole;
import roles.BottomRole;
import roles.TopRole;


public class BackConverter {

	public BackConverter() {

	}
	

	private OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	private OWLDataFactory factory = manager.getOWLDataFactory();
	
	public Set<OWLEntity> getClassfromConcept(Set<AtomicConcept> concept_set) {
		
		Set<OWLEntity> d_sig = new LinkedHashSet<>();
		
		for (AtomicConcept concept : concept_set) {
			d_sig.add(getClassfromConcept(concept));
		}
		
		return d_sig;
	}
	
	public OWLEntity getClassfromConcept(AtomicConcept concept) {
				
		OWLEntity owlentity = factory.getOWLEntity(EntityType.OBJECT_PROPERTY, IRI.create(concept.getText()));
		
		return owlentity;
	}
	
	public List<Formula> toAxiomsList(List<Formula> input_list) throws CloneNotSupportedException {
		
		List<Formula> output_list = new ArrayList<>();
		for (Formula clause : input_list) {
			if (clause == BottomConcept.getInstance()) {						
				return Collections.singletonList(toInclusion(BottomConcept.getInstance()));	
				
			} else if (clause != TopConcept.getInstance()) {
				//Simplifier pp = new Simplifier();
				//Formula el_clause = pp.removeDoubleNegations(toELH(clause));
				//Formula el_clause = pp.removeDoubleNegations(clause);
				Formula axiom = toInclusion(clause);
				output_list.add(axiom);
			}
		}
		
		if (output_list.isEmpty()) {			
			output_list.add(toInclusion(TopConcept.getInstance()));
		}
				
		Set<Formula> output_set = new LinkedHashSet<>(output_list);
		output_list.clear();
		output_list.addAll(output_set);
		
		return output_list;
	}
	
	public Set<Formula> toAxioms(List<Formula> input_list) throws CloneNotSupportedException {
		
		Set<Formula> output_set = new LinkedHashSet<>();
		for (Formula clause : input_list) {
			if (clause == BottomConcept.getInstance() || clause == BottomRole.getInstance()) {									
				return Collections.singleton(toInclusion(BottomConcept.getInstance()));
				
			} else if (clause != TopConcept.getInstance() && clause != TopRole.getInstance()) {
				//PreProcessor pp = new PreProcessor();
				//Formula el_clause = pp.removeDoubleNegations(toELH(clause));
				Formula axiom = toInclusion(clause);
				output_set.add(axiom);
			}
		}
				
		return output_set;
	}
	
	
	private Formula toInclusion(Formula formula) {

		if (formula instanceof Inclusion) {
			return formula;

		} else {
			return new Inclusion(TopConcept.getInstance(), formula);
		}

	}

	/*
	private Formula toAxiom(Formula formula) {
		
		if (formula instanceof Inclusion) {
			return formula;
			
		} else if (formula instanceof Or) {

			EChecker ec = new EChecker();
			if (ec.hasRole(formula) && !ec.hasRoleRestriction(formula)) {

				List<Formula> negative_list = new ArrayList<>();
				List<Formula> positive_list = new ArrayList<>();
				List<Formula> disjunct_list = formula.getSubFormulas();
				for (Formula disjunct : disjunct_list) {
					if (disjunct instanceof Negation) {
						negative_list.add(disjunct.getSubFormulas().get(0));
					} else {
						positive_list.add(disjunct);
					}
				}

				Formula lefthand = null;
				if (negative_list.isEmpty()) {
					lefthand = TopRole.getInstance();
				} else if (negative_list.size() == 1) {
					lefthand = negative_list.get(0);
				} else {
					lefthand = new And(negative_list);
				}

				Formula righthand = null;
				if (positive_list.isEmpty()) {
					righthand = BottomRole.getInstance();
				} else if (positive_list.size() == 1) {
					righthand = positive_list.get(0);
				} else {
					righthand = new Or(positive_list);
				}		

				return new Inclusion(lefthand, righthand);

			} else {

				List<Formula> negative_list = new ArrayList<>();
				List<Formula> positive_list = new ArrayList<>();
				List<Formula> disjunct_list = formula.getSubFormulas();
				for (Formula disjunct : disjunct_list) {
					if (disjunct instanceof Negation && disjunct.getSubFormulas().get(0) instanceof Individual) {
						negative_list.clear();
						positive_list.clear();
						negative_list.add(disjunct.getSubFormulas().get(0));
						disjunct_list.remove(disjunct);
						positive_list.addAll(disjunct_list);
						break;
					} else {
						if (disjunct instanceof Negation) {
							negative_list.add(disjunct.getSubFormulas().get(0));
						} else {
							positive_list.add(disjunct);
						}
					}
				}

				Formula lefthand = null;
				if (negative_list.isEmpty()) {
					lefthand = TopConcept.getInstance();
				} else if (negative_list.size() == 1) {
					lefthand = negative_list.get(0);
				} else {
					lefthand = new And(negative_list);
				}

				Formula righthand = null;
				if (positive_list.isEmpty()) {
					righthand = BottomConcept.getInstance();
				} else if (positive_list.size() == 1) {
					righthand = positive_list.get(0);
				} else {
					righthand = new Or(positive_list);
				}

				return new Inclusion(lefthand, righthand);
			}

		} else if (formula instanceof Negation) {

			if (formula.getSubFormulas().get(0) instanceof AtomicRole) {
				return new Inclusion(formula.getSubFormulas().get(0), BottomRole.getInstance());
			} else {
				return new Inclusion(formula.getSubFormulas().get(0), BottomConcept.getInstance());
			}

		} else if (formula instanceof AtomicRole) {
			return new Inclusion(TopRole.getInstance(), formula);
			
		} else {
			return new Inclusion(TopConcept.getInstance(), formula);
		}

	}	*/
	
	/*private Formula toALC(Formula formula) throws CloneNotSupportedException {
		
		if (formula instanceof Negation) {
			formula.getSubFormulas().set(0, toALC(formula.getSubFormulas().get(0)));
			return formula;

		} else if (formula instanceof Exists || formula instanceof Forall) {
			formula.getSubFormulas().set(1, toALC(formula.getSubFormulas().get(1)));
			return formula;

		} else if (formula instanceof And || formula instanceof Or) {
			List<Formula> conjunct_list = formula.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(toALC(conjunct));
			}
			return new And(new_conjunct_list);
			
		} else if (formula instanceof Inclusion || formula instanceof Equivalence) {
			formula.getSubFormulas().set(0, toALC(formula.getSubFormulas().get(0)));
			formula.getSubFormulas().set(1, toALC(formula.getSubFormulas().get(1)));
			return formula;
		}

		return formula;
	}
	
	private Formula toELH(Formula formula) throws CloneNotSupportedException {
						
		if (formula instanceof Negation) {
			formula.getSubFormulas().set(0, toELH(formula.getSubFormulas().get(0)));
			return formula;

		} else if (formula instanceof Exists) {
			formula.getSubFormulas().set(1, toELH(formula.getSubFormulas().get(1)));
			return formula;

		} else if (formula instanceof Forall) {
			return new Negation(
					new Exists(formula.getSubFormulas().get(0), toELH(new Negation(formula.getSubFormulas().get(1)))));

		} else if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(toELH(conjunct));
			}
			return new And(new_conjunct_list);
			
		} else if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(toELH(disjunct));
			}
			return new Or(new_disjunct_list);
			
		} else if (formula instanceof Inclusion || formula instanceof Equivalence) {
			formula.getSubFormulas().set(0, toELH(formula.getSubFormulas().get(0)));
			formula.getSubFormulas().set(1, toELH(formula.getSubFormulas().get(1)));
			return formula;
		}

		return formula;
	}*/
	
	/**
	 * else if (formula instanceof Or) {
			//System.out.println("Or = " + formula);
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(toELH(new Negation(disjunct)));
			}
			return new Negation(new And(new_disjunct_list));
			
		}
	 * @param
	 * @return
	 */
	
	/*public Formula toPreAxioms(Formula formula) throws CloneNotSupportedException {

		while (!(formula.equals(toPreAxiom(formula)))) {
			formula = toPreAxiom(formula);
		}
		
		return formula;
	}
	
	private Formula toPreAxiom(final Formula input) throws CloneNotSupportedException {
		
		Formula formula = input.clone();
		
		EChecker ec = new EChecker();
		
		if (formula == BottomConcept.getInstance()) {
			return new Negation(TopConcept.getInstance());
			
		} else if (formula instanceof Negation) {
			formula.getSubFormulas().set(0, toPreAxiom(formula.getSubFormulas().get(0)));
			return formula;

		} else if (formula instanceof Exists) {
			if (formula.getSubFormulas().get(1) instanceof Negation) {
				return new Negation(new Forall(formula.getSubFormulas().get(0),
						toPreAxiom(formula.getSubFormulas().get(1).getSubFormulas().get(0))));
			} else {
				formula.getSubFormulas().set(1, toPreAxiom(formula.getSubFormulas().get(1)));
				return formula;
			}

		} else if (formula instanceof Forall) {
			if (formula.getSubFormulas().get(1) instanceof Negation) {
				return new Negation(new Exists(formula.getSubFormulas().get(0),
						toPreAxiom(formula.getSubFormulas().get(1).getSubFormulas().get(0))));
			} else {
				formula.getSubFormulas().set(1, toPreAxiom(formula.getSubFormulas().get(1)));
				return formula;
			}

		} else if (formula instanceof And) {
						
			if (ec.allNegationsInside(formula)) {
				
				List<Formula> conjunct_list = formula.getSubFormulas();
				List<Formula> new_conjunct_list = new ArrayList<>();
				for (Formula conjunct : conjunct_list) {
					new_conjunct_list.add(toPreAxiom(conjunct.getSubFormulas().get(0)));
				}				
				return new Negation(new Or(new_conjunct_list));
				
			} else {
				
				List<Formula> conjunct_list = formula.getSubFormulas();
				List<Formula> new_conjunct_list = new ArrayList<>();
				for (Formula conjunct : conjunct_list) {
					new_conjunct_list.add(toPreAxiom(conjunct));
				}
				return new And(new_conjunct_list);				
			}
			
		} else if (formula instanceof Or) {
			
			if (ec.allNegationsInside(formula)) {
				
				List<Formula> disjunct_list = formula.getSubFormulas();
				List<Formula> new_disjunct_list = new ArrayList<>();
				for (Formula disjunct : disjunct_list) {
					new_disjunct_list.add(toPreAxiom(disjunct.getSubFormulas().get(0)));
				}				
				return new Negation(new And(new_disjunct_list));
				
			} else {
				
				List<Formula> disjunct_list = formula.getSubFormulas();
				List<Formula> new_disjunct_list = new ArrayList<>();
				for (Formula disjunct : disjunct_list) {
					new_disjunct_list.add(toPreAxiom(disjunct));
				}
				return new Or(new_disjunct_list);				
			}
		}

		return formula;
	}*/
	
	public OWLOntology toOWLSubClassOfAxiomOntology(List<Formula> formula_list) throws OWLOntologyCreationException {

		OWLOntology ontology = manager.createOntology(IRI.generateDocumentIRI());

		for (Formula formula : formula_list) {
			manager.addAxiom(ontology, toOWLSubClassOfAxiom(formula));
		}

		return ontology;
	}


	public OWLOntology toOWLOntology(List<Formula> formula_list) throws OWLOntologyCreationException {

		OWLOntology ontology = manager.createOntology();

		for (Formula formula : formula_list) {
			manager.addAxiom(ontology, toOWLAxiom(formula));
		}

		return ontology;
	}
	
	public Set<OWLAxiom> toOWLAxioms(List<Formula> formula_set) {

		Set<OWLAxiom> output_set = new LinkedHashSet<>();
		
		for (Formula formula : formula_set) {
			output_set.add(toOWLAxiom(formula));
		}

		return output_set;
	}
	
	
	public OWLAxiom toOWLSubClassOfAxiom(Formula inclusion) {
		
		OWLSubClassOfAxiom scoa = factory.getOWLSubClassOfAxiom(toOWLClassExpression(inclusion.getSubFormulas().get(0)),
					toOWLClassExpression(inclusion.getSubFormulas().get(1)));
		
		return scoa;
	}

	public OWLAxiom toOWLAxiom(Formula inclusion) {
		//RBox
		Formula subsumee = inclusion.getSubFormulas().get(0);
		
		if (subsumee instanceof AtomicRole) {
			return factory.getOWLSubObjectPropertyOfAxiom(
					toOWLObjectPropertyExpression(inclusion.getSubFormulas().get(0)),
					toOWLObjectPropertyExpression(inclusion.getSubFormulas().get(1)));
		//ABox
		} else {
			return factory.getOWLSubClassOfAxiom(toOWLClassExpression(inclusion.getSubFormulas().get(0)),
					toOWLClassExpression(inclusion.getSubFormulas().get(1)));
		}

	}
	
	/*
	 * else if (inclusion.getSubFormulas().get(0) instanceof Individual) {
			if (inclusion.getSubFormulas().get(1) instanceof Exists
					&& inclusion.getSubFormulas().get(1).getSubFormulas().get(1) instanceof Individual) {
				return factory.getOWLObjectPropertyAssertionAxiom(
						toOWLObjectPropertyExpression(inclusion.getSubFormulas().get(1).getSubFormulas().get(0)),
						toOWLNamedIndividual(inclusion.getSubFormulas().get(0)),
						toOWLNamedIndividual(inclusion.getSubFormulas().get(1).getSubFormulas().get(1)));
			} else {
				return factory.getOWLClassAssertionAxiom(toOWLClassExpression(inclusion.getSubFormulas().get(1)),
						toOWLNamedIndividual(inclusion.getSubFormulas().get(0)));
			}
		//TBox
		} 
	 * 
	 */
	
	public OWLClassExpression toOWLClassExpression(Formula formula) {

		if (formula == TopConcept.getInstance()) {
			return factory.getOWLThing();
		} else if (formula instanceof AtomicConcept) {
			OWLClass owlClass = factory.getOWLClass(IRI.create(formula.getText()));
			return owlClass;
		} else if (formula instanceof Exists) {
			return factory.getOWLObjectSomeValuesFrom(
					toOWLObjectPropertyExpression(formula.getSubFormulas().get(0)),
					toOWLClassExpression(formula.getSubFormulas().get(1)));
		} else if (formula instanceof And) {
			Set<OWLClassExpression> conjunct_set = new LinkedHashSet<>();
			Set<Formula> new_conjunct_set = formula.getSubformulae();
			for (Formula conjunct : new_conjunct_set) {
				conjunct_set.add(toOWLClassExpression(conjunct));
			}
			return factory.getOWLObjectIntersectionOf(conjunct_set);
		}

		assert false : "Unsupported ClassExpression: " + formula;
		return null;
	}

	public OWLObjectPropertyExpression toOWLObjectPropertyExpression(Formula role) {
		
		//System.out.println("role = " + role);
		//System.out.println("role class = " + role.getClass());

        if (role instanceof AtomicRole) {
		    return factory.getOWLObjectProperty(IRI.create(role.getText()));
		}

		assert false : "Unsupported ObjectPropertyExpression: " + role;
		return null;
	}
	
	public OWLNamedIndividual toOWLNamedIndividual(Formula Indi) {

		if (Indi instanceof Individual) {
			return factory.getOWLNamedIndividual(IRI.create(Indi.getText()));
		}

		assert false : "Unsupported ObjectPropertyExpression: " + Indi;
		return null;
	}

}
