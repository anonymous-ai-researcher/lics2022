# README
## 【Update】the script of analyzing the connection between timeout and maxDepth

* The file OxfordAnalyse.txt and BioPortalAnalyse.txt are the meta data. Run the script main.py and get the result of the Table 3 in our paper.
## Welcome
* Welcome to this site and thanks for your interest in trying out our uniform interpolation (UI) tool and logical difference (UI-Diff) tool. Both tools are implemented in Java using the **OWL API**, so to get them work, first make sure you have JDK/JRE installed on your machine.
* Your feedbacks are always welcome!

## Semantic difference between SNOMED CT ontologies

* ![image](https://github.com/anonymous-ai-researcher/lics2022/blob/master/information_gain_and_loss.jpg)

## GUI

* We would also like to invite the reviewers/users to try out user-friendly web access to these tools via [here](http://www.forgettingshow.info).

## Environment requirement

* JDK 1.8
* IDE: IDEA 
* Maven

## Data

* All the test data, including Oxford-ISG snapshot, BioPortal snapshot,  SNOMED CT and GO, can be downloaded at https://github.com/anonymous-ai-researcher/lics2022.

## Import of this project

* Unzip this project.
* Import it into IDEA.
* Make the src folder as source root.
* Make sure that the jar package under the root folder has been added into project as libriaries.

## Description of the UI tool

* The UI tool is a high-performance prototype for computing uniform interpolants of **ELH-Ontologies**. It can be used as a Java library or a standalone tool for UI and related tasks.

* A uniform interpolant is a restricted view of an ontology that uses only a sub-signature of the ontology, namely, the interpolation signature, while preserving all logical entailments over the interpolation signature. A uniform interpolant can be computed by forgetting the names (usually incrementally) not  in the interpolation signature (the set of the names to be forgotten is called the forgetting signature) in such a way that all logical entailments are preserved up to the remaining signature, which amounts to the interpolation signature.

* Our UI tool can always compute a uniform interpolant for ELH-Ontologies. If an input ontology is not an ELH one, our tool simply takes the ELH fragment of the ontology and discards those axioms not expressible in ELH. If an input ontology contains cyclic dependencies over the names in the forgetting signature, the result cannot always be represented finitely without fixpoint operators. Since fixpoint operators are not supported by OWL API, our UI tool introduces additional concept names, namely definers, to the output ontology that simulate the behaviour of fixpoint operators. In this sense, the result is no longer a uniform interpolant, since it contains extra names that are not in the specified interpolation signature.

## Run of the UI tool

* To run the forgetting method, go to  **/src/forgetting/Forgetter.class** and call the method: 

  ```java
  public Set<OWLAxiom> ForgettingAPI(Set<OWLObjectProperty> roles, Set<OWLClass> concepts, OWLOntology onto)
  ```

* The input are a set of role names to be forgotten  ( ``` Set<OWLObjectProperty> roles ``` ),  a set of concept names to be forgotten ( ``` Set<OWLClass> concepts ``` ) and an ELH-Ontologies from which the concept and role names are forgotten ( ``` OWLOntology onto ``` ).

* The output is another ELH-Ontology which is a Σ-uniform interpolant of the ontology ``onto``, represented as a set of OWLAxioms.

* An example illustrating the usage of the UI tool is included in the Forgetter.class main function.

## Description of the UI-Diff tool

* The UI-Diff tool is a high-performance prototype for computing a finite representation of the logical difference **UI-Diff(O1, O2)** between two ELH-Ontologies O1 and O2. The tool implements a two-step algorithm with the **first step** computing a Σ-uniform interpolant V2 of O2 for Σ = sig(O1) ∩ sig(O2) using the UI tool, and the **second step** computing the UI-witness set W2 by collecting all axioms α ∈ V2 with O1 ⊭ α using the DL reasoner HermiT.

* As a third step, it may be useful to partition the UI-witnesses into explicit and implicit UI-witnesses. An explicit UI-witness is the one that is originally contained in O2. An implicit UI-witness is the one that is originally not contained in O2, but entailed by O2. Implicit UI-witnesses are generated by uniform interpolation.

* UI-Diff(O1, O2) computes the information gain from O1 to O2, or information loss from O2 to O1. So if one wants to compute the information gain from O2 to O1 (information loss from O1 to O2), just swap the places of O1 and O2, i.e., **UI-Diff(O2, O1)**.

## Run of the UI-Diff tool

* To run the UI-Diff method, go to **/src/forgetting/LDiff.class**, and call the method:

  ```java
  public void compute_LDiff(OWLOntology onto_1, OWLOntology onto_2, String path)
  ```

* The input are two ELH-Ontologies O1 ( ```onto_1``` ), O2 ( ```onto_2``` )  and a ```path``` specifying the location where you want the output to be locally saved.

* The output are a set of UI-witnesses, a set of explicit UI-witnesses and a set of implicit UI-witnesses, all represented as .owl files. 
* An example illustrating the usage of the UI-Diff tool is included in the LDiff.class main function.

