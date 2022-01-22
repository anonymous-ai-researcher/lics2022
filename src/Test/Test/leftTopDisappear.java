package Test.Test;

import concepts.AtomicConcept;
import convertion.BackConverter;
import formula.Formula;
import org.junit.Test;
import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import roles.AtomicRole;
import connectives.*;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.sql.Connection;
import java.sql.Driver;
import java.sql.DriverManager;
import java.util.*;

public class leftTopDisappear {
    @Test
    public void test0()throws Exception {
        Set<OWLEntity> forgettingSigs = getForgettingSig("/Users/liuzhao/Desktop/dermlex_ver_1_0.owl.txt");
        OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();

        OWLOntology onto  = manager1.loadOntologyFromOntologyDocument(new File("/Users/liuzhao/Desktop/dermlex_ver_1_0.owl"));
        for(OWLLogicalAxiom axiom : onto.getLogicalAxioms()){
            if(axiom instanceof OWLEquivalentClassesAxiom || axiom instanceof OWLSubClassOfAxiom  ||
            axiom instanceof OWLEquivalentObjectPropertiesAxiom || axiom instanceof  OWLSubObjectPropertyOfAxiom ||
            axiom instanceof OWLObjectPropertyRangeAxiom || axiom instanceof OWLObjectPropertyDomainAxiom)
                System.out.println(axiom);
        }
        Map<Integer,Integer> map = new HashMap<>();
    }

    Set<OWLEntity> getForgettingSig(String path)throws Exception{
        OWLDataFactory factory = OWLManager.getOWLDataFactory();
        BufferedReader sigReader = new BufferedReader(new FileReader(
                new File(path)));
        String tmp = "";
        Set<OWLEntity> forgettingSignatures = new HashSet<>();

        while ((tmp = sigReader.readLine()) != null) {
            System.out.println("load signatures:");

            Set<OWLClass> randomSampledConcepts = new HashSet<>();
            Set<OWLObjectProperty> randomSampledRoles = new HashSet<>();

            tmp = tmp.trim();
            String[] line = tmp.split(",");
            for (String owlEntity : line) {
                if (owlEntity.startsWith("Concept") || owlEntity.startsWith("Role")) {
                    String type = owlEntity.split("\\|")[0];
                    String ent = owlEntity.split("\\|")[1];
                    if (type.equals("Concept")) {
                        randomSampledConcepts.add(factory.getOWLClass(IRI.create(ent)));
                    } else if (type.equals("Role")) {
                        randomSampledRoles.add(factory.getOWLObjectProperty(IRI.create(ent)));
                    }
                }
            }


            System.out.println("signatures loaded successfully.");
            forgettingSignatures.addAll(randomSampledConcepts);
            forgettingSignatures.addAll(randomSampledRoles);
            System.out.println(forgettingSignatures);
          //  return forgettingSignatures;
        }
        return forgettingSignatures;
    }
    @Test
    public void test1()throws Exception{
        AtomicConcept a = new AtomicConcept("A");
        AtomicConcept c = new AtomicConcept("C");

        AtomicConcept d = new AtomicConcept("D");
        AtomicConcept f = new AtomicConcept("F");
        AtomicConcept g = new AtomicConcept("G");
        AtomicRole r = new AtomicRole("r");
        Set<Formula> set = new HashSet<>();
        set.add(a);
        set.add(d);
        Formula and = And.getAnd(set);
        Formula f1 = new Exists(r,and);
        Formula F1 = new Inclusion(c,f1);
        Set<Formula> set2 = new HashSet<>();
        set2.add(a);
        set2.add(f);
        Formula and2 = And.getAnd(set2);
        Formula F2 = new Inclusion(and2,g);
        Formula F3 = new Inclusion(d,f);
        BackConverter bc = new BackConverter();
        OWLAxiom axiom1 = bc.toOWLAxiom(F1);
        OWLAxiom axiom2 = bc.toOWLAxiom(F2);
        OWLAxiom axiom3 = bc.toOWLAxiom(F3);
        System.out.println(axiom1);
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        Set<OWLAxiom> axioms = new HashSet<>();
        axioms.add(axiom1);axioms.add(axiom2);axioms.add(axiom3);
        OWLOntology now = manager.createOntology(axioms);
        System.out.println(now.getLogicalAxioms());
        OWLReasoner hermit = new ReasonerFactory().createReasoner(now);
        Formula f2 = new Negation(f);
        Formula F4 = new Inclusion(f2,g);
        OWLAxiom axiom4 = bc.toOWLAxiom(F4);
        System.out.println(axiom4);
        System.out.println(hermit.isEntailed(axiom4));
        System.out.println(f2);
    }

    @Test
    public void test4()throws  Exception{
        Thread.sleep(100000);
        Thread t = new Thread(new sleep(),"sleepmy");
        t.start();
        Thread.sleep(2000);
        t.interrupt();
        Thread.sleep(1000);
        System.out.println(t.isInterrupted());
    }
    class sleep implements Runnable{
        @Override
        public void run(){
            while(true){
                try {
                    Thread.sleep(10000);
                }catch (Exception e){
                    System.out.println("Ex");
                }

            }
        }
    }
    @Test
    public  void test5() throws Exception{
        ServiceLoader<Driver> loader = ServiceLoader.load(Driver.class);

        // JDK 的类加载器所能寻找到的所有驱动
        Iterator<Driver> iterator = loader.iterator();

        while (iterator.hasNext()) {
            Driver driver = iterator.next();

            System.out.println("driver : " + driver.getClass() + " , loader : " + driver.getClass().getClassLoader());
        }
        String url = "jdbc:mysql://localhost:3306/jdbctest";
// 通过java库获取数据库连接
        Connection conn = DriverManager.getConnection(url,"liuzhao","Lz990087");
    }
    @Test
    public void test6(){
        String str = new String("33");
        String temp = str.intern();
        System.out.println(temp == str);
        String s1 = new StringBuilder("计算机").append("软件").toString();
        System.out.println(s1.intern() == s1);
    }



}
