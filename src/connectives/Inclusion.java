/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package connectives;

import java.util.HashSet;
import java.util.*;

import com.google.common.collect.Sets;

import concepts.AtomicConcept;
import formula.Formula;
import roles.AtomicRole;

/**
 *
 * @author Yizheng
 */
public class Inclusion extends Formula {

	public Inclusion() {
		super();
	}

	public Inclusion(Formula subsumee, Formula subsumer) {
		super(2);
		this.setSubFormulas(subsumee, subsumer);
		/*this.c_sig = new HashSet<>();
		this.r_sig = new HashSet<>();
		this.set_c_sig(subsumee.get_c_sig());
		this.set_c_sig(subsumer.get_c_sig());
		this.set_r_sig(subsumee.get_r_sig());
		this.set_r_sig(subsumer.get_r_sig());*/
	}
	
	public Set<AtomicConcept> get_c_sig() {	
		Formula subsumee = this.getSubFormulas().get(0);
		Formula subsumer = this.getSubFormulas().get(1);
		return Sets.union(subsumee.get_c_sig(), subsumer.get_c_sig());
	}
	
	public Set<AtomicRole> get_r_sig() {
		Formula subsumee = this.getSubFormulas().get(0);
		Formula subsumer = this.getSubFormulas().get(1);
		return Sets.union(subsumee.get_r_sig(), subsumer.get_r_sig());
	}
	
	public static void main(String[] args) {

		AtomicConcept a = new AtomicConcept("A");
		AtomicConcept b = new AtomicConcept("B");
		AtomicConcept c = new AtomicConcept("C");
		AtomicRole r = new AtomicRole("r");
		Exists e = new Exists(r, b);
		Set<Formula> list = new LinkedHashSet<>();
		list.add(a);
		list.add(c);
		And and = new And(list);
		Inclusion inc = new Inclusion(e, and);
		System.out.println(inc);
		System.out.println("e.c_sig = " + e.get_c_sig());
		System.out.println("e.r_sig = " + e.get_r_sig());
		System.out.println("and.c_sig = " + and.get_c_sig());
		System.out.println("and.r_sig = " + and.get_r_sig());
		System.out.println("inc.c_sig = " + inc.get_c_sig());
		System.out.println("inc.r_sig = " + inc.r_sig);
		
	}
	

	@Override
	public String toString() {
		Formula subsumee = this.getSubFormulas().get(0);
		Formula subsumer = this.getSubFormulas().get(1);
		return subsumee + " \u2291 " + subsumer;
	}

}
