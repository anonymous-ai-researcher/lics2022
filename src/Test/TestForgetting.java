package Test;
import java.io.*;
import java.util.*;

import checkexistence.EChecker;
import checkfrequency.FChecker;
import com.google.common.collect.Sets;
import concepts.AtomicConcept;
import concepts.TopConcept;
import convertion.BackConverter;
import convertion.Converter;
import forgetting.*;
import formula.Formula;
import inference.Inferencer;
import javafx.fxml.LoadException;
import org.semanticweb.HermiT.*;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.util.NullProgressMonitor;
import roles.AtomicRole;
import sun.misc.FormattedFloatingDecimal;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;
import elk.*;
import connectives.*;
import com.google.common.collect.*;
import java.util.concurrent.*;
import uk.ac.man.cs.lethe.forgetting.AlchTBoxForgetter;

import javax.swing.text.html.parser.Entity;

public class TestForgetting {
    static int aaai22Test = 1;
    public static ArrayList<String> getFileName(String path){
        ArrayList<String> listFileName = new ArrayList<>();
        File file =new File(path);
        String[] names= file.list();
        for(String name : names){
            listFileName.add(path+name);
        }
        return listFileName;
    }
    public static void saveUI(Set<OWLAxiom> ui, String path)throws Exception{

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology now = manager.createOntology(ui);
        OutputStream ops = new FileOutputStream(new File(path));
        manager.saveOntology(now, ops);
    }
    public static List<OWLObjectProperty> getSubStringByRadom1(List<OWLObjectProperty> list, int count){
        List backList = null;
        backList = new ArrayList<OWLObjectProperty>();
        Random random = new Random();
        int backSum = 0;
        if (list.size() >= count) {
            backSum = count;
        }else {
            backSum = list.size();
        }
        for (int i = 0; i < backSum; i++) {
//			随机数的范围为0-list.size()-1
            int target = random.nextInt(list.size());
            backList.add(list.get(target));
        }
        return backList;
    }
    public static List<OWLClass> getSubStringByRadom2(List<OWLClass> list, int count){
        List backList = null;
        backList = new ArrayList<OWLClass>();
        Random random = new Random();
        int backSum = 0;
        if (list.size() >= count) {
            backSum = count;
        }else {
            backSum = list.size();
        }
        for (int i = 0; i < backSum; i++) {
//			随机数的 ≤./范围为0-list.size()-1
            int target = random.nextInt(list.size());
            backList.add(list.get(target));
        }
        return backList;
    }
    public static int afterForgettingAxiomsSize = 0;
    public static int beforeForgettingAxiomsSize = 0;
    public static OWLOntology onto = null;
    public static double time = 0;
    public static int isExtra = 0;
    public static double mem = 0;
    public static int success = 0;
    public static  int witness_explicit_onto = 0;
    public static  int witness_implicit_onto  = 0;
    public static String nowLog = null;
    public static OWLOntology resultOWLOntology;
    public static int isExtra(OWLOntology resultontology){
        Set<OWLClass> conceptn = resultontology.getClassesInSignature();
        for (OWLClass concept : conceptn) {
            if (concept.getIRI().getShortForm().startsWith("_D")){
                System.out.println(concept.getIRI().getShortForm());
                return 1;
            }
        }
        return 0;
    }
    public static OWLOntology LetheForgetting(String dictPath,String filelog,String log,Set<OWLEntity> symbols,OWLOntology onto) throws Exception{

        final ExecutorService exec = Executors.newSingleThreadExecutor();
        AlchTBoxForgetter LetheForgetter = new AlchTBoxForgetter();
        Callable<Integer> task = new Callable<Integer>() {
            @Override
            public Integer call() throws Exception {
                try {
                    isExtra = 0;
                    success = 1;
                    System.gc();
                    Runtime r = Runtime.getRuntime();
                    long mem1 = r.freeMemory();
                    List<Formula> beginFormulalist = new Converter().OntologyConverter(onto);
                    long time1 = System.currentTimeMillis();
                    resultOWLOntology = LetheForgetter.forget(onto,symbols);
                    isExtra = isExtra(resultOWLOntology);
                    long time2 = System.currentTimeMillis();
                    long mem2 = r.freeMemory();
                    //elkEntailment.check(onto,resultOWLOntology,symbols);
                    if(success == 1 && isExtra == 0){

                        List<Formula> ui = new Converter().OntologyConverter(resultOWLOntology);
                        System.out.println(resultOWLOntology.getLogicalAxiomCount());
                        afterForgettingAxiomsSize = Sets.difference(new HashSet<>(ui),new HashSet<>(beginFormulalist)).size();
                        beforeForgettingAxiomsSize = Sets.difference(new HashSet<>(beginFormulalist),new HashSet<>(ui)).size();
                        System.out.println(afterForgettingAxiomsSize+" "+beforeForgettingAxiomsSize);

                        time = (time2 - time1);
                        mem = (mem1-mem2);
                    }

                } catch (OutOfMemoryError e){
                    if(aaai22Test != 1)
                        writeFile.writeFile(dictPath+filelog,"1,"+log  +",0,0,0,1,0,0,0,0\n");
                    System.err.println("outofmemory");
                    success = 0;
                }

                catch (StackOverflowError e){
                    if(aaai22Test != 1)
                        writeFile.writeFile(dictPath+filelog,"1,"+log  +",0,0,0,1,0,0,0,0\n");
                    System.err.println("stackoverflow");
                    success = 0;
                }catch (Exception e){
                    System.err.println(e+"runtimeerror");
                    writeFile.writeFile(dictPath+filelog,"run time error lethe\n");

                    success = 0;
                }
                return 1;
            }
        };
        Future<Integer> future = exec.submit(task);
        try{
            int t = future.get(1000 * 500,TimeUnit.MILLISECONDS);
        }
        catch (OutOfMemoryError e){
            if(aaai22Test != 1)
                writeFile.writeFile(dictPath+filelog,"1,"+log  +",0,0,0,1,0,0,0,0\n");
            System.err.println("outofmemory2");
            success = 0;
        }

        catch (TimeoutException e){
            if(aaai22Test != 1)
                writeFile.writeFile(dictPath+filelog,"1,"+log+",0,0,1,0,0,0,0,0\n");
            else{
                writeFile.writeFile(dictPath+"timeout.txt","timeout lethe\n");
                System.err.println("timeout");

            }
            success = 0;
        }

        if(success == 1 && isExtra == 0 ){
            if(aaai22Test != 1)
                writeFile.writeFile(dictPath+filelog,"1,"+log+","+time*1.0+","+mem/1024/1024+",0,0,1,0,"+afterForgettingAxiomsSize+","+beforeForgettingAxiomsSize+"\n");
            else{
                writeFile.writeFile(dictPath+filelog,log+",lethe,"+time*1.0+","+mem/1024/1024+","+
                        resultOWLOntology.getLogicalAxiomCount()+","+afterForgettingAxiomsSize+","+beforeForgettingAxiomsSize+"\n");
            }
        }
        if(success == 1 && isExtra != 0){
            if(aaai22Test != 1)
                writeFile.writeFile(dictPath+filelog,"1,"+log+",0,0,0,0,0,1,0,0\n");
            else{
                writeFile.writeFile(dictPath+"extra.txt","lethe extra\n");
            }
        }
        return resultOWLOntology;
    }


    public static OWLOntology MyForgetting(String dictPath,String filelog,String log, Set<OWLObjectProperty> roleSet, Set<OWLClass> conceptSet,OWLOntology onto) throws  Exception{
        final ExecutorService exec = Executors.newSingleThreadExecutor();
        Callable<Integer> task = new Callable<Integer>() {
            @Override
            public Integer call() throws Exception {
                try {
                    isExtra = 0;
                    success = 1;
                    System.gc();
                    Runtime r = Runtime.getRuntime();
                    long mem1 = r.freeMemory();
                    List<Formula> beginFormulalist = new Converter().OntologyConverter(onto);
                    long time1 = System.currentTimeMillis();

                    List<Formula> ui = new Forgetter().Forgetting(roleSet, conceptSet, onto);
                    resultOWLOntology = new BackConverter().toOWLOntology(ui);

                    long time2 = System.currentTimeMillis();
                    long mem2 = r.freeMemory();
                    if(success == 1 && isExtra == 0){
                        afterForgettingAxiomsSize = Sets.difference(new HashSet<>(ui),new HashSet<>(beginFormulalist)).size();
                        beforeForgettingAxiomsSize = Sets.difference(new HashSet<>(beginFormulalist),new HashSet<>(ui)).size();
                        time = (time2 - time1);
                        mem = (mem1-mem2);
                        //elkEntailment.check(onto,ui,roleSet,conceptSet);

                    }


                } catch (OutOfMemoryError e){
                    if(aaai22Test != 1)
                        writeFile.writeFile(dictPath+filelog,"0,"+log  +",0,0,0,1,0,0,0,0,0\n");
                    System.err.println("outofmemory");
                    success = 0;
                }

                catch (StackOverflowError e){
                    if(aaai22Test != 1)
                        writeFile.writeFile(dictPath+filelog,"0,"+log  +",0,0,0,1,0,0,0,0,0\n");
                    System.err.println("stackoverflow");
                    success = 0;
                }
                return 1;
            }
        };
        Future<Integer> future = exec.submit(task);
        try{
            int t = future.get(1000 * 35000,TimeUnit.MILLISECONDS);
        }
        catch (OutOfMemoryError e){
            if(aaai22Test != 1)
                writeFile.writeFile(dictPath+filelog,"0,"+log  +",0,0,0,1,0,0,0,0,0\n");
            System.err.println("outofmemory2");
            success = 0;
        }
        catch (TimeoutException e){
            if(aaai22Test != 1){
                writeFile.writeFile(dictPath+filelog,"0,"+log+",0,0,1,0,0,0,0,0,0\n");
            }else{
                writeFile.writeFile(dictPath+"timeout.txt","timeout mine\n");

                System.err.println("timeout");

            }

            success = 0;
        }

        if(success == 1 && isExtra == 0 ){
            if(aaai22Test != 1){
                writeFile.writeFile(dictPath+filelog,"0,"+log+","+time*1.0+","+mem/1024/1024+",0,0,1,0,"+afterForgettingAxiomsSize+","+beforeForgettingAxiomsSize+","+AtomicConcept.getDefiner_index()+"\n");
            }else{
                writeFile.writeFile(dictPath+filelog,log+",prototype,"+time*1.0+","+mem/1024/1024+","+
                        resultOWLOntology.getLogicalAxiomCount()+","+afterForgettingAxiomsSize+","+beforeForgettingAxiomsSize+","+AtomicConcept.getDefiner_index()+"\n");
            }
        }
        if(success == 1 && isExtra != 0){
            if(aaai22Test != 1){
                writeFile.writeFile(dictPath+filelog,"0,"+log+",0,0,0,0,0,1,0,0,0\n");
            }else{
                writeFile.writeFile(dictPath+"extra.txt","mine extra\n");
            }
        }
        return resultOWLOntology;
    }
    public static void saveOntology(OWLOntologyManager manager2,OWLOntology onto,String path)throws Exception{
        OWLOntology myForgettingUIsave = manager2.createOntology();
        for(OWLLogicalAxiom axiom : onto.getLogicalAxioms())
            manager2.applyChange(new AddAxiom(myForgettingUIsave, axiom));
        manager2.saveOntology(myForgettingUIsave,new FileOutputStream(new File(path)));
    }
    // return is the number of witness
    public static int checkWitnessAndSave(OWLOntologyManager manager, OWLOntology onto1, OWLOntology V, String uiSavePath)throws Exception{
        int number = 0;
        OWLOntology witness = manager.createOntology();
        OWLReasoner reasoner = null;
        try {
             reasoner = new ReasonerFactory().createReasoner(onto1);


        }catch (Exception e){
            System.err.println("HERMIT error");
            return -1;
        }
        Set<OWLLogicalAxiom> now = V.getLogicalAxioms();
        now.removeAll(onto1.getLogicalAxioms());
        int i = 0;
        try {
            for (OWLLogicalAxiom axiom : now) {
                if (!reasoner.isEntailed(axiom)) {
                    number++;
                    manager.applyChange(new AddAxiom(witness, axiom));
                }
                System.out.println("check " + i++ + " " + now.size());
            }
        }catch (Exception e){
            System.err.println("entail error");
            reasoner.dispose();
            return -3;
        }
        catch (Error e){
            System.err.println("Java heap space");
            reasoner.dispose();
            return -4;
        }
        manager.saveOntology(witness, new FileOutputStream(new File(uiSavePath)));
        System.out.println("witness number: "+number);
        reasoner.dispose();
        return number;
    }

    public static void testLdBetweenMineAndLethe(String dictPath,String pathOnto1,String pathOnto2 )throws Exception{
        if(dictPath.charAt(dictPath.length()-1) != '/') dictPath += "/";
        String title = "file,tool,time,mem,uisize,afterForgettingAxiomsSize,beforeForgettingAxiomsSize,definersSize";
        //String dictPath = "/Users/liuzhao/Desktop/NCBO/CVDO/";
        //String pathOnto1 = "2016.owl";
        //String pathOnto2 = "2020.owl";
        String filelog = "log"+"_8.24aiiitest.txt";
        Converter ct = new Converter();
        BackConverter bc = new BackConverter();
        OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
        OWLOntologyManager manager2 = OWLManager.createOWLOntologyManager();
        OWLOntology onto1 = null,onto2 = null;
        try {
            System.out.println("begin loaded");
            long now = System.currentTimeMillis();
            onto1 = manager1.loadOntologyFromOntologyDocument(new File(pathOnto1));
            System.out.println("onto1 load time " + (System.currentTimeMillis() - now));
            System.out.println("onto1 loaded");
            onto2 = manager2.loadOntologyFromOntologyDocument(new File(pathOnto2));
            System.out.println("onto2 loaded");
        }catch (Exception e) {
            System.err.println(dictPath+" IO error");
            writeFile.writeFile(dictPath+"errorIO2.txt"," IO error"+'\n');
            return;
        }


        /*
        //data
        List<Formula> formulaELH = ct.OntologyConverter(onto2);
        onto2 = bc.toOWLOntology(formulaELH);
         */
        //final String log = dictPath+","+logicalsize+","+rolesize+","+conceptsize+","+GCIsize+","+GCIrolesize+","+GCIconceptsize+",";
        final String log = pathOnto2;
        time = 0;
        mem = 0;
        afterForgettingAxiomsSize = 0;
        beforeForgettingAxiomsSize = 0;
        elkEntailment.hasChecked_OnO2.clear();
        AtomicConcept.setDefiner_index(1);
        Set<OWLClass> forgettingConcepts = new LinkedHashSet<>(Sets.difference(onto2.getClassesInSignature(), onto1.getClassesInSignature()));
        Set<OWLObjectProperty> forgettingRoles = new LinkedHashSet<>(Sets.difference(onto2.getObjectPropertiesInSignature(), onto1.getObjectPropertiesInSignature()));
        Set<OWLEntity> forgettingSignatures = Sets.union(new HashSet<>(forgettingConcepts), new HashSet<>(forgettingRoles));
        /*
        SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager1, onto2, ModuleType.STAR);
        Set<OWLAxiom> moduleOnto_2OnForgettingSig = extractor.extract(Sets.difference(onto2.getSignature(), forgettingSignatures));
        Set<OWLLogicalAxiom> moduleOnto_2OnCommonSig_logical = new HashSet<>();
        Set<OWLAxiom> moduleOnto_2OnCommonSig2 = new HashSet<>();
        System.out.println("module finished");
        for (OWLAxiom axiom : moduleOnto_2OnForgettingSig) {
            if (axiom instanceof OWLLogicalAxiom) {
                moduleOnto_2OnCommonSig_logical.add((OWLLogicalAxiom) axiom);
                moduleOnto_2OnCommonSig2.add(axiom);
            }
        }
        OWLOntology afterDeleteNotELHAxioms = manager2.createOntology(moduleOnto_2OnCommonSig2);
        List<Formula> formulaList = ct.AxiomsConverter(moduleOnto_2OnCommonSig_logical);

         */

        System.out.println("begin mine");
        OWLOntology myForgettingUI = MyForgetting(dictPath,filelog,log,new HashSet<>(forgettingRoles),new HashSet<>(forgettingConcepts),onto2);
        int number1 = -1;
        if(success == 1 && isExtra == 0) {
            saveOntology(manager2, myForgettingUI, dictPath + "uiPrototype.owl");
            number1 = checkWitnessAndSave(manager2, onto1, myForgettingUI, dictPath + "witnessPrototype.owl");
            if (number1 < 0) {
                writeFile.writeFile(dictPath + "hermiterror.txt",number1 + " "+'\n');
                return;
            }
        }
        writeFile.writeFile(dictPath + filelog, number1 + " " + '\n');





        System.out.println("begin lethe");
        OWLOntology letheForgettingUI = LetheForgetting(dictPath,filelog,log,forgettingSignatures,onto2);
        int number2 = -1;
        if(success == 1 && isExtra == 0) {
            saveOntology(manager2, letheForgettingUI, dictPath + "uiLethe.owl");
            number2 = checkWitnessAndSave(manager2, onto1, letheForgettingUI, dictPath + "witnessLethe.owl");


        }
        writeFile.writeFile(dictPath+filelog,number2+" "+'\n');


        // check witness in letheui and mineui
/*
        //check if lethe can entail mine
        OWLReasoner reasoner = new Reasoner(new Configuration(),letheForgettingUI);
        int number = 0 ;
        for(OWLAxiom axiom : myForgettingUI.getLogicalAxioms()){
            number++;
            System.out.println(axiom);
            if(!reasoner.isEntailed(axiom)){
                throw new Exception("not entailed");
            }else{
                System.out.println(number+" "+myForgettingUI.getLogicalAxioms().size());
            }
        }
        reasoner.dispose();
        System.out.println("good! myUI is entailed by LetheUI!");
        */

    }

    public static void testUI(String corpus)throws Exception{
        String dictPath = "/Users/liuzhao/Desktop/experiments/Test_data_for_forgetting/TestData/"+corpus+"/";
        //String dictPath = "/Users/liuzhao/nju/NCBO/data/";
        double rate = 0.3;
        String filelog = "log"+rate+corpus+"_8.11test.txt";
        String title = "isLethe,fileName,LogicalAxiomsSize,RolesSize,ConceptsSize,GCISize,GCIRolesSize,GCIConceptSize,rate,time,memory,timeOut,MemoryOut," +"isSuccess,isExtra,afterForgettingAxiomsSize,beforeForgettingAxiomsSize\n";
       //writeFile.writeFile(dictPath+filelog,title);//写入title
        Converter ct = new Converter();
        BackConverter bc = new BackConverter();
        int circle = 3;//重复10次实验
        int isLethe = 0;
        ArrayList<String> allFile = getFileName(dictPath);
        //ArrayList<String> allFile = readFile.readFile(dictPath+corpus+".txt");
        for(String path : allFile){
            if(!path.contains(".owl")) continue;
            int hasReadMine = 0;
            ArrayList<String> hasRecord = readFile.readFile(dictPath+filelog);
            for(String temp : hasRecord) {
                if (temp.contains(path) && (temp.charAt(0)- (int)('1')) == 0) {
                    hasReadMine++;
                }

            }
            if(hasReadMine >= circle) continue;
            System.out.println("File:"+path);

            for( ; hasReadMine < circle ; hasReadMine++){
                OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
                onto = manager1.loadOntologyFromOntologyDocument(new File(path));

                // 统计基本的信息
                int logicalsize = onto.getLogicalAxioms().size();
                int rolesize = onto.getObjectPropertiesInSignature().size();
                int conceptsize = onto.getClassesInSignature().size();
                int GCIsize = onto.getGeneralClassAxioms().size();
                Set<OWLClassAxiom> GCIs = onto.getGeneralClassAxioms();
                Set<OWLObjectProperty> GCIroles = new LinkedHashSet<>();
                Set<OWLClass> GCIconcepts = new LinkedHashSet<>();
                for(OWLClassAxiom axiom : GCIs){
                    GCIconcepts.addAll(axiom.getClassesInSignature());
                    GCIroles.addAll(axiom.getObjectPropertiesInSignature());
                }
                int GCIrolesize = GCIroles.size();
                int GCIconceptsize = GCIconcepts.size();

                //data
                List<Formula> formulaELH = ct.OntologyConverter(onto);
                onto = bc.toOWLOntology(formulaELH);
                Set<OWLClass>concepts = onto.getClassesInSignature();
                Set<OWLObjectProperty>roles = onto.getObjectPropertiesInSignature();
                List<OWLClass> conceptList = new ArrayList<>(concepts);
                List<OWLObjectProperty>roleList = new ArrayList<>(roles);
                final String log = path+","+logicalsize+","+rolesize+","+conceptsize+","+GCIsize+","+GCIrolesize+","+GCIconceptsize+","+rate;
                time = 0;
                mem = 0;
                afterForgettingAxiomsSize = 0;
                beforeForgettingAxiomsSize = 0;
                elkEntailment.hasChecked_OnO2.clear();
                AtomicConcept.setDefiner_index(1);
                System.out.println("forgetting roles :"+(int) (rate * rolesize));
                System.out.println("forgetting concepts :"+(int) (rate * conceptsize));
                System.out.println(hasReadMine);
                List<OWLClass> forgettingConcepts = getSubStringByRadom2(conceptList, (int) (rate * conceptsize));
                List<OWLObjectProperty> forgettingRoles = getSubStringByRadom1(roleList, (int) (rate * rolesize));

                /*
                  Set<OWLEntity> forgettingSignatures = Sets.union(new HashSet<>(forgettingConcepts), new HashSet<>(forgettingRoles));
                SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager1, onto, ModuleType.STAR);
                Set<OWLAxiom> moduleOnto_2OnForgettingSig = extractor.extract(Sets.difference(onto.getSignature(), forgettingSignatures));
                Set<OWLLogicalAxiom> moduleOnto_2OnCommonSig_logical = new HashSet<>();
                System.out.println("module finished");
                for (OWLAxiom axiom : moduleOnto_2OnForgettingSig) {
                    if (axiom instanceof OWLLogicalAxiom) {
                        moduleOnto_2OnCommonSig_logical.add((OWLLogicalAxiom) axiom);
                    }
                }
                List<Formula> formulaList = ct.AxiomsConverter(moduleOnto_2OnCommonSig_logical);

                 */
                System.out.println("begin mine");
                OWLOntology myForgettingUI = MyForgetting(dictPath,filelog,log,new HashSet<>(forgettingRoles),new HashSet<>(forgettingConcepts),onto);
                System.out.println("begin lethe");
                //OWLOntology letheForgettingUI = LetheForgetting(dictPath,filelog,log,formulaList,forgettingSignatures,onto);
                /*
                       OWLReasoner      reasoner = new ReasonerFactory().createReasoner(letheForgettingUI);

                int number = 0 ;
                for(OWLAxiom axiom : myForgettingUI.getLogicalAxioms()){
                    number++;
                    System.out.println(axiom);
                    if(!reasoner.isEntailed(axiom)){
                        throw new Exception("not entailed");
                    }else{
                        System.out.println(number+" "+myForgettingUI.getLogicalAxioms().size());
                    }
                }
                System.out.println(letheForgettingUI.getLogicalAxiomCount()+" "+onto.getLogicalAxiomCount());
                System.out.println("good! myUI is entailed by LetheUI!");

                 */
            }


        }
    }
    public static OWLOntology checkWitness(OWLOntology onto1,OWLOntology onto2,OWLOntology ui,String pathlog,String witnesspath)throws Exception{
        System.out.println("starting reasoning");
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        Set<OWLClass> c_sig_1 = onto1.getClassesInSignature();
        Set<OWLClass> c_sig_2 = onto2.getClassesInSignature();
        Set<OWLClass> c_sig = new LinkedHashSet<>(Sets.difference(c_sig_2, c_sig_1));
        Set<OWLObjectProperty> r_sig_1 = onto1.getObjectPropertiesInSignature();
        Set<OWLObjectProperty> r_sig_2 = onto2.getObjectPropertiesInSignature();
        Set<OWLObjectProperty> r_sig = new LinkedHashSet<>(Sets.difference(r_sig_2, r_sig_1));

        Set<OWLEntity> forgettingSignatures = new HashSet<>();
        forgettingSignatures.addAll(r_sig);
        forgettingSignatures.addAll(c_sig);
        int uisize = ui.getLogicalAxiomCount();
        Set<OWLLogicalAxiom> uiSet = ui.getLogicalAxioms();
        // as we compute the uniform_interpolant on module, we must add the axioms in O2 with no new signatures because they may be explicit witness.
        for(OWLLogicalAxiom axiom : onto2.getLogicalAxioms()){
            if(Sets.intersection(axiom.getSignature(),forgettingSignatures).size() == 0 ){
                uiSet.add(axiom);
            }
        }
        int num_add_all_commonSig_axioms_fromO2 = uiSet.size();
        uiSet = Sets.difference(uiSet,onto1.getLogicalAxioms());
        int numadd_all_commonSig_axioms_fromO2_subO1 = uiSet.size();
        System.out.println(uisize+" "+num_add_all_commonSig_axioms_fromO2+" "+numadd_all_commonSig_axioms_fromO2_subO1);
        OWLOntology witness_complete_onto = manager.createOntology();
        OWLOntology witness_explicit_onto = manager.createOntology();
        OWLOntology witness_implicit_onto = manager.createOntology();
        //OWLReasoner hermit =  new ElkReasonerFactory().createReasoner(onto1);
        OWLReasoner hermit=new ReasonerFactory().createReasoner(onto1);
        int numexplicit = 0;
        int numimplicit = 0;
        int step = 0;
        int all = uiSet.size();
        for(OWLAxiom axiom:uiSet){
            step++;
            //if(elkEntailment.entailed(hermit,axiom)){
               // BiMap<String, Integer> biMap = HashBiMap.create();
                if(hermit.isEntailed(axiom)){

            }
            else{
                manager.applyChange(new AddAxiom(witness_complete_onto, axiom));
                if(onto2.getAxioms().contains(axiom)){
                    manager.applyChange(new AddAxiom(witness_explicit_onto, axiom));

                    numexplicit++;
                    System.out.println("explicit "+numexplicit);

                }
                else{
                    manager.applyChange(new AddAxiom(witness_implicit_onto, axiom));
                    numimplicit++;
                    System.out.println("implicit "+numimplicit);
                }

            }
            System.out.println(step+" "+all);
        }

        writeFile.writeFile(pathlog,numexplicit+","+numimplicit+"\n");
        System.out.println(numexplicit+","+numimplicit+","+num_add_all_commonSig_axioms_fromO2+","+numadd_all_commonSig_axioms_fromO2_subO1+"\n");
        OutputStream os_complete;
        OutputStream os_explicit;
        OutputStream os_implicit;
        os_complete = new FileOutputStream(new File(witnesspath + "_witness_complete.owl"));
        manager.saveOntology(witness_complete_onto, os_complete);
        os_explicit = new FileOutputStream(new File(witnesspath + "_witness_explicit.owl"));
        manager.saveOntology(witness_explicit_onto, os_explicit);
        os_implicit = new FileOutputStream(new File(witnesspath + "_witness_implicit.owl"));
        manager.saveOntology(witness_implicit_onto, os_implicit);

        return witness_complete_onto;
    }
    public static void mergeWitness(OWLOntology implicitwitness,OWLOntology explicitwitness,String log){
        HashMap<Formula,HashSet<Formula>> map = new HashMap<>();
        Converter ct = new Converter();
        List<Formula> formula_list = ct.OntologyConverter(implicitwitness);
        int step = 0;
        for(Formula formula : formula_list){
            step++;
            Formula l1 = formula.getSubFormulas().get(0);
            Formula r1 = formula.getSubFormulas().get(1);
            if(map.containsKey(l1)){
                if(r1 instanceof And){
                    map.get(l1).addAll(r1.getSubformulae());
                }
                else map.get(l1).add(r1);

            }
            else{
                if(r1 instanceof And){
                    HashSet<Formula> temp = new HashSet<>();
                    temp.addAll(r1.getSubformulae());
                    map.put(l1,temp);
                }
                else{
                    HashSet<Formula> temp = new HashSet<>();
                    temp.add(r1);
                    map.put(l1,temp);
                }
            }
        }
        System.out.println("-------");
        BackConverter bc = new BackConverter();
        List<Formula> afterMerge = new ArrayList<>();
        for(Formula key : map.keySet()){
            HashSet<Formula>and = map.get(key);
            Formula r = null;
            if(and.size() > 1)
                r =  And.getAnd(and);
            for(Formula f: and){
                r  = f;
            }
            Formula inclusion = new Inclusion(key,r);
            afterMerge.add(inclusion);

        }
        Set<OWLAxiom> ui = bc.toOWLAxioms(afterMerge);
        int implicit = Sets.difference(ui,explicitwitness.getLogicalAxioms()).size();
        System.out.println(implicit);
        System.out.println(ui.size());
    }
    public static void check3(String name)throws Exception{
        String dictPath = "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/";
        OWLOntology onto =  OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(dictPath+name));
        System.out.println("loaded");

        Converter ct = new Converter();
        List<Formula> list = ct.OntologyConverter(onto);
        int num = 0;
        System.out.println("started");
        for(Formula formula : list){
            if(formula.getSubFormulas().get(1) instanceof TopConcept)
                num++;
        }
        System.out.println(num);
    }

    public static void choose(){
        String dictPath = "/Users/liuzhao/nju/NCBO/data/log0.1corpus1_n.txt";
        List<String> now = readFile.readFile(dictPath);
        String last = "owl";
        String tagPath = "/Users/liuzhao/nju/NCBO/data/log0.1corpus1_n_temp.txt";

        for(String s1: now){
            int t1 = s1.indexOf("owl");
            int t2 = last.indexOf("owl");
            if(t1 == t2){

            }
            else{
                writeFile.writeFile(tagPath,s1+"\n");

            }
            last = s1;

        }
    }
    public static void statistics()throws Exception{
        String defner = "http://snomed.info/id/128289001";
        String dictPath = "/Users/liuzhao/Desktop/";
        AtomicConcept concept= new AtomicConcept(defner);
        OWLOntology onto = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(dictPath+"ontology_201707.owl"));
        int pos = 0, neg = 0;
        FChecker ec = new FChecker();
        EChecker ec2 = new EChecker();
        List<Formula> formulas = new Converter().OntologyConverter(onto);
        int step = 0;
        Set<Formula> positive_star_premises = new LinkedHashSet<>(); // C in A   1
        Set<Formula> positive_exists_premises = new LinkedHashSet<>(); //  C in exist r. A   2
        Set<Formula> positive_exists_and_premises = new LinkedHashSet<>(); //  C in exist r. (A and B)   3
        Set<Formula> negative_star_premises = new LinkedHashSet<>(); // A in G  4
        Set<Formula> negative_star_and_premises = new LinkedHashSet<>(); // A and F in G  5
        Set<Formula> negative_exists_premises = new LinkedHashSet<>(); //  exist r. A in G   6
        Set<Formula> negative_star_and_exists_premises = new LinkedHashSet<>(); // exists r.A and F in G   7
        Set<Formula> negative_exists_and_premises = new LinkedHashSet<>(); //  exist r. (A and D) in G   8
        Set<Formula> negative_star_and_exists_and_premises = new LinkedHashSet<>(); //  exist r. (A and D) and F in G   9
        for(Formula formula: formulas){
            pos+= ec.positive(concept,formula);
            neg+= ec.negative(concept,formula);
            System.out.println(formulas.size()+" "+step);
            step++;
            Formula subsumee = formula.getSubFormulas().get(0);
            Formula subsumer = formula.getSubFormulas().get(1);
            if (!ec2.isPresent(concept, formula)) {

            }
            if (subsumer.equals(concept)) {
                positive_star_premises.add(formula);

            }
            if (subsumer instanceof Exists &&
                    ec2.isPresent(concept, subsumer)) {

                if(subsumer.getSubFormulas().get(1).equals(concept))positive_exists_premises.add(formula);
                else positive_exists_and_premises.add(formula);

            }
            if (subsumee.equals(concept)) {
                negative_star_premises.add(formula);

            }
            if (subsumee instanceof And) {
                if (subsumee.getSubformulae().contains(concept)) { ////// changed
                    negative_star_and_premises.add(formula);
                }

                for(Formula f : subsumee.getSubformulae()){
                    if(ec2.isPresent(concept,f)){
                        System.out.println(subsumee);
                        if(f.getSubFormulas().get(1).equals(concept)){
                            negative_star_and_exists_premises.add(formula);
                        }
                        else{
                            negative_star_and_exists_and_premises.add(formula);
                        }
                    }
                }


            }
            if (subsumee instanceof Exists) {
                if(subsumee.getSubFormulas().get(1).equals(concept)) negative_exists_premises.add(formula);
                else negative_exists_and_premises.add(formula);

            }
        }
        System.out.println(pos+" "+neg);
        System.out.println("1  "+ positive_star_premises.size());
        System.out.println("1  "+ positive_exists_premises.size());

        System.out.println("1  "+ positive_exists_and_premises.size());

        System.out.println("1  "+ negative_star_premises.size());

        System.out.println("1  "+ negative_star_and_premises.size());
        System.out.println("1  "+ negative_exists_premises.size());
        System.out.println("1  "+ negative_star_and_exists_premises.size());
        System.out.println("1  "+ negative_exists_and_premises.size());
        System.out.println("1  "+ negative_star_and_exists_and_premises.size());
    }
    public static void statisticsBio() throws Exception{

        List<Integer> tbox = new ArrayList<>();
        List<Integer> Nc = new ArrayList<>();
        List<Integer> Nr = new ArrayList<>();

        String dictPath = "/Users/liuzhao/nju/NCBO/data/PART3/";
        List<String> now = getFileName(dictPath);
        int sum1 = 0,sum2 = 0,sum3 = 0;
        for(String s: now){
            OWLOntology onto = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(s));
            Nr.add(onto.getObjectPropertiesInSignature().size());
            Nc.add(onto.getClassesInSignature().size());
            tbox.add(onto.getLogicalAxiomCount());
            sum1+=onto.getClassesInSignature().size();
            sum2+=onto.getObjectPropertiesInSignature().size();
            sum3+=onto.getLogicalAxiomCount();

        }
        Collections.sort(tbox);
        Collections.sort(Nc);
        Collections.sort(Nr);
        int a = Nc.get(0), b = Nc.get(Nc.size()-1);
        System.out.println(a+" "+b);
        List<Integer> l1 = Nc.subList((int)(Nc.size()*0.1),Nc.size());
        int sum = 0;
        for(Integer i : l1 ){
            sum+=i;
        }

        sum = sum/l1.size();
        System.out.println(Nc.get(0)+" "+Nc.get(Nc.size()-1)+" "+Nc.get(Nc.size()/2)+" "+sum1/Nc.size()+" "+sum);
        List<Integer> l2 = Nr.subList((int)(Nr.size()*0.1),Nr.size());
        sum = 0;
        for(Integer i : l2 ){
            sum+=i;
        }
        sum = sum/l2.size();
        System.out.println(Nr.get(0)+" "+Nr.get(Nr.size()-1)+" "+Nr.get(Nr.size()/2)+" "+sum2/Nr.size()+" "+sum);
        List<Integer> l3 = tbox.subList((int)(tbox.size()*0.1),tbox.size());
        sum = 0;
        for(Integer i : l3 ){
            sum+=i;
        }
        sum = sum/l3.size();
        System.out.println(tbox.get(0)+" "+tbox.get(tbox.size()-1)+" "+tbox.get(tbox.size()/2)+" "+sum3/tbox.size()+" "+sum);

    }
    public static List<OWLOntology> testLDiff(String dictPath,String nameonto1,String nameonto2)throws Exception{
        String filelog = "logtemp"+".txt";
        ArrayList<String> hasRecord = readFile.readFile(dictPath+filelog);

        String title = "fileName_O1,fileName_O2,LogicalAxiomsSize_O1,LogicalAxiomsSize_O2,RolesSize_O1,RolesSize_O2,ConceptsSize_O1,ConceptsSize_O2," +
                "GCISize_O1,GCISize_O2,GCIRolesSize_O1,GCIRolesSize_O2,GCIConceptSize_O1,GCIConceptSize_O2,newLogicalRoleSize,newLogicalConceptSize,newLogicalRoleSizeOccuredInGCI,newLogicalConceptSizeOccuredInGCI,time," +
                "memory,timeOut,MemoryOut," +"isSuccess,isExtra,UI_size,explicit_witness,implicit_witness\n";
        // writeFile.writeFile(dictPath+filelog,title);
        Converter ct = new Converter();
        BackConverter bc = new BackConverter();
        ArrayList<String> now = getFileName(dictPath);
        List<OWLOntology> ans = new ArrayList<>();
        for(String path : now) {
            for (String path2 : now) {
                if(path.equals(path2)) continue;
                int hasRead = 0;
                for (String temp : hasRecord) {
                    if (temp.contains(path+","+path2)) {
                        hasRead = 1;
                        break;
                    }
                }

                //if(path.contains("202001")) continue;
                if(!(path.contains(nameonto1) && path2.contains(nameonto2))) continue;

                if (hasRead == 1) continue;
                if (!path.contains(".owl") || !path2.contains(".owl")) continue;
                OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
                String pathuiNCIT = dictPath+path.substring(path.length()-9,path.length()-4)+path2.substring(path2.length()-9,path2.length()-4)+"temp2.owl";
                System.out.println(pathuiNCIT);
                System.out.println(path);
                System.out.println(path2);

                OWLOntology onto1 = manager1.loadOntologyFromOntologyDocument(new File(path));
                System.out.println("onto1 load1");
                // 统计基本的信息
                int logicalsize1 = onto1.getLogicalAxioms().size();
                int rolesize1 = onto1.getObjectPropertiesInSignature().size();
                int conceptsize1 = onto1.getClassesInSignature().size();
                int GCIsize1 = onto1.getGeneralClassAxioms().size();
                Set<OWLClassAxiom> GCIs1 = onto1.getGeneralClassAxioms();
                Set<OWLObjectProperty> GCIroles1 = new LinkedHashSet<>();
                Set<OWLClass> GCIconcepts1 = new LinkedHashSet<>();
                for (OWLClassAxiom axiom : GCIs1) {
                    GCIconcepts1.addAll(axiom.getClassesInSignature());
                    GCIroles1.addAll(axiom.getObjectPropertiesInSignature());
                }
                int GCIrolesize1 = GCIroles1.size();
                int GCIconceptsize1 = GCIconcepts1.size();


                OWLOntologyManager manager2 = OWLManager.createOWLOntologyManager();
                OWLOntology onto2 = manager2.loadOntologyFromOntologyDocument(new File(path2));
                System.out.println("onto2 load1");
                // 统计基本的信息
                int logicalsize2 = onto2.getLogicalAxioms().size();
                int rolesize2 = onto2.getObjectPropertiesInSignature().size();
                int conceptsize2 = onto2.getClassesInSignature().size();
                int GCIsize2 = onto2.getGeneralClassAxioms().size();
                Set<OWLClassAxiom> GCIs2 = onto2.getGeneralClassAxioms();
                Set<OWLObjectProperty> GCIroles2 = new LinkedHashSet<>();
                Set<OWLClass> GCIconcepts2 = new LinkedHashSet<>();
                for (OWLClassAxiom axiom : GCIs2) {
                    GCIconcepts2.addAll(axiom.getClassesInSignature());
                    GCIroles2.addAll(axiom.getObjectPropertiesInSignature());
                }
                int GCIrolesize2 = GCIroles2.size();
                int GCIconceptsize2 = GCIconcepts2.size();


                //data

                Set<OWLClass> concepts1 = onto1.getClassesInSignature();
                Set<OWLObjectProperty> roles1 = onto1.getObjectPropertiesInSignature();

                Set<OWLClass> concepts2 = onto2.getClassesInSignature();
                Set<OWLObjectProperty> roles2 = onto2.getObjectPropertiesInSignature();

                //diff data

                Set<OWLClass> c_sig = new LinkedHashSet<>(Sets.difference(concepts2, concepts1));
                Set<OWLObjectProperty> r_sig = new LinkedHashSet<>(Sets.difference(roles2, roles1));
                Set<AtomicRole> role_set = ct.getRolesfromObjectProperties(r_sig);
                Set<AtomicConcept> concept_set = ct.getConceptsfromClasses(c_sig);
                Set<OWLEntity> forgettingSignatures = new HashSet<>();
                forgettingSignatures.addAll(r_sig);
                forgettingSignatures.addAll(c_sig);

                String log = path + "," + path2+","+logicalsize1 + "," +logicalsize2+","+ rolesize1 + "," +rolesize2+","+
                        conceptsize1 + "," +conceptsize2+","+ GCIsize1 + "," + GCIsize2 + "," +GCIrolesize1 + "," +GCIrolesize2 + "," +
                        GCIconceptsize1 + ","+ GCIconceptsize2 + ","+ Sets.difference(roles2,roles1).size()+","+Sets.difference(concepts2,concepts1).size()+","+
                        Sets.intersection(GCIroles2, Sets.difference(roles2,roles1)).size()+","+Sets.intersection(GCIconcepts2, Sets.difference(concepts2,concepts1)).size();

                System.out.println("gci " +GCIsize2);
                nowLog = log ;
                System.out.println(nowLog);
                time = 0;
                mem = 0;
                afterForgettingAxiomsSize = 0;
                Forgetter fg = new Forgetter();
                isExtra = 0;
                success = 1;
                witness_explicit_onto = 0;
                witness_implicit_onto = 0;
                elkEntailment.hasChecked_OnO2 = new HashMap<>();
                AtomicConcept.setDefiner_index(1);
                SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager1, onto2, ModuleType.STAR);
                Set<OWLAxiom> moduleOnto_2OnCommonSig = extractor.extract(Sets.difference(onto2.getSignature(),forgettingSignatures));
                Set<OWLLogicalAxiom> moduleOnto_2OnCommonSig_logical = new HashSet<>();
                for (OWLAxiom axiom : moduleOnto_2OnCommonSig) {
                    if (axiom instanceof OWLLogicalAxiom) {
                        moduleOnto_2OnCommonSig_logical.add((OWLLogicalAxiom) axiom);
                    }
                }
                System.out.println(moduleOnto_2OnCommonSig_logical.size()+" "+moduleOnto_2OnCommonSig.size());
                System.out.println("module finished");
                List<Formula> formulaList = ct.AxiomsConverter(moduleOnto_2OnCommonSig_logical);
                try {
                    System.gc();
                    Runtime r = Runtime.getRuntime();
                    long mem1 = r.freeMemory();
                    long time1 = System.currentTimeMillis();
                    System.out.println("The forgetting task is to eliminate [" + concept_set.size() + "] concept names and ["
                            + role_set.size() + "] role names from [" + moduleOnto_2OnCommonSig_logical.size() + "] normalized axioms");
                    List<Formula> ui = fg.Forgetting(r_sig, c_sig, onto2);

                    long time2 = System.currentTimeMillis();
                    long mem2 = r.freeMemory();
                    //elkEntailment.check(onto2,ui);
                    time += (time2 - time1);
                    mem += (mem1 - mem2);
                    Set<OWLAxiom> uniform_interpolant = bc.toOWLAxioms(ui);
                    saveUI(uniform_interpolant,pathuiNCIT);
                    ans.add(onto1);
                    ans.add(onto2);
                    ans.add(bc.toOWLOntology(ui));
                    afterForgettingAxiomsSize = uniform_interpolant.size();


                } catch (OutOfMemoryError e) {
                    nowLog = nowLog + ",0,0,0,1,0,0,0,0,0\n";
                    writeFile.writeFile(dictPath + filelog, nowLog);
                    System.err.println("outofmemory");
                    e.printStackTrace();
                    success = 0;
                } catch (StackOverflowError e) {
                    nowLog = nowLog + ",0,0,0,2,0,0,0,0,0\n";
                    writeFile.writeFile(dictPath + filelog, nowLog);
                    System.err.println("stackoverflow");
                    success = 0;
                }



                if (success == 1 && isExtra == 0) {
                    nowLog = nowLog + "," + time  + "," + mem / 1024 / 1024  + ",0,0,1,0," + afterForgettingAxiomsSize  + ",";
                    writeFile.writeFile(dictPath + filelog, nowLog);


                }


                if (success == 1 && isExtra != 0) {
                    nowLog = nowLog + ",0,0,0,0,0," + isExtra + ",0,0,0\n";
                    writeFile.writeFile(dictPath + filelog, nowLog);
                }

            }

        }
        return ans;
    }
    public static void testLethe() throws Exception{
        AlchTBoxForgetter letheForgetter = new AlchTBoxForgetter();
        OWLOntology onto1 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File("/Users/liuzhao/Desktop/experiments/Test_data_for_forgetting/dataSet/Oxford-ISG/PARTIII/00117.owl"));
        Set<OWLEntity> symbols = new HashSet<>();
        for(OWLClass o : onto1.getClassesInSignature()){
            symbols.add(o);
            break;
        }
        letheForgetter.forget(onto1,symbols);
    }
    public static void testGhadah()throws Exception{
        OWLOntology onto1 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File("/Users/liuzhao/Desktop/go-2021-02-01.owl"));
        OWLOntology itui = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File("/Users/liuzhao/Desktop/goslim_agr.owl"));
        Set<OWLEntity> symbols = Sets.difference(onto1.getSignature(),itui.getSignature());
       // List<Formula> beginFormulalist = new Converter().OntologyConverter(onto1);
        Set<OWLClass> conceptSet = new HashSet<>();
        Set<OWLObjectProperty> roleSet = new HashSet<>();
        System.out.println(symbols.size());
        for(OWLEntity entity : symbols){
            if(entity instanceof OWLClass) conceptSet.add((OWLClass)entity);
            else if(entity instanceof  OWLObjectProperty) roleSet.add((OWLObjectProperty) entity);
        }
        System.out.println(conceptSet.size()+" "+roleSet.size());
        List<Formula> ui = new Forgetter().Forgetting(roleSet, conceptSet, onto1);


    }
    public static void testAAAI22()throws Exception{
        ArrayList<String> allFile = getFileName("/Users/liuzhao/Desktop/NCBOcrawler/ECSO/");
        int twoToolsFinished = 0;
        int empty = 0;
        for(String dictPath : allFile){
            int temp = 0;
            System.out.println(dictPath);
            try {
                ArrayList<String> owlName = getFileName(dictPath+"/");
                if(owlName.size() == 0) empty++;
                String onto1="",onto2 = "";
                int finished = 0;
                for(String file : owlName){
                    if(file.contains("newliuzhao.owl")){
                        onto2 = file;
                    }else if(file.contains("oldliuzhao.owl")){
                        onto1 = file;
                    }else if(file.contains("uiPrototype.owl") || (file.contains(".txt") && !file.contains("errorIO.txt")) || file.contains("errorIO2.txt")){
                        finished = 1;
                    }
                    if(file.contains("witnessPrototype.owl") || file.contains("witnessLethe.owl")){
                        temp++;
                    }
                    if(file.contains("hermiterror.txt")) finished  = 0;

                }
                if(temp == 2) twoToolsFinished++;
                if(finished == 1)continue;
                if(onto1.contains("oldliuzhao.owl") && onto2.contains("newliuzhao.owl")){
                    System.out.println(onto1+" "+onto2);
                    testLdBetweenMineAndLethe(dictPath,onto1,onto2);
                }
            }catch (NullPointerException n){
                System.out.println();
            }

        }
        System.out.println(empty);
        System.out.println(twoToolsFinished);
    }
    public static void testDefinedConceptsNums() throws Exception{
        OWLOntology on = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(
                "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/ontology_202007.owl"));
        Set<OWLClass> classes = on.getClassesInSignature();
        Set<OWLLogicalAxiom> axioms = on.getLogicalAxioms();
        Set<OWLClass> left = new HashSet<>();
        Set<OWLClass> right = new HashSet<>();
        for(OWLLogicalAxiom axiom : axioms){
            if(axiom instanceof OWLEquivalentClassesAxiom){
                OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
                Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlECA.asOWLSubClassOfAxioms();
                for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
                    left.addAll(owlSCOA.getSubClass().getClassesInSignature());
                    right.addAll(owlSCOA.getSuperClass().getClassesInSignature());
                    break;
                }
            }else if(axiom instanceof  OWLSubClassOfAxiom){
                OWLSubClassOfAxiom owlSCOA = (OWLSubClassOfAxiom) axiom;
                left.addAll(owlSCOA.getSubClass().getClassesInSignature());
                right.addAll(owlSCOA.getSuperClass().getClassesInSignature());
            }
        }
        int leftsize = left.size();
        left.removeAll(right);
        System.out.println(classes.size()+" "+leftsize+" "+right.size() + " "+left.size() +" "+(left.size()*1.0/classes.size()));

    }
    public static void staticalAAAI22()throws Exception{
        ArrayList<String> allFile = getFileName("/Users/liuzhao/Desktop/NCBOcrawler/");
        int success = 0;
        int empty = 0;
        int errorIO = 0;
        int hermitError = 0;
        int extra = 0;
        int timeout = 0;
        int files = 0;
        int runtimeerror = 0;
        int equal = 0;
        for(String dictPath : allFile){
            System.out.println(dictPath);
            if(dictPath.contains(".DS_Store")) continue;
            files++;
            ArrayList<String> owlName = getFileName(dictPath+"/");
            if(owlName.size() == 0) {
                empty++;
                continue;
            }
            int tempfinished = 0;
            int temphermitError  =0;
            int temperrorIO = 0;
            int tempextra = 0;
            int temptimeout = 0;
            for(String file : owlName){
                if(file.contains("errorIO.txt") || file.contains("errorIO2.txt")){
                    temperrorIO++;
                }else if(file.contains("hermiterror.txt")){
                    temphermitError++;
                }else if(file.contains("timeout.txt")){
                    temptimeout++;
                }else if(file.contains("extra.txt")){
                    tempextra++;
                }else if(file.contains("log_8.24aiiitest.txt"))
                    tempfinished++;


            }
            if(temphermitError == 0 && temperrorIO == 0 && tempextra == 0 && temptimeout == 0 && tempfinished != 0 ) {
                success++;
                BufferedReader br = new BufferedReader(new FileReader(dictPath+"/log_8.24aiiitest.txt"));

                String line = null;
                int t1  =-10,t2 = -10, linePos = 0;
                int tag = 0;
                while ((line = br.readLine()) != null) {
                    if(linePos == 1) t1 =Integer.parseInt(line.replace(" ",""));
                    if(linePos == 3) t2 = Integer.parseInt(line.replace(" ",""));
                    if(line.contains("error")){
                        tag = 1;
                        break;

                    }
                    linePos++;
                }
                if(tag == 1){
                    success--;
                    runtimeerror++;
                }
                if(t1 >= 0 && t2 >= 0 && t1 != t2){
                    System.err.println("different " + dictPath);

                }else if(t1 >= 0 && t2 >= 0 && t1 == t2)equal++;

                br.close();
            }
            else if(temphermitError != 0) hermitError++;
            else if(temperrorIO != 0) errorIO++;
            else if(tempextra != 0) extra++;
            else if(temptimeout != 0) timeout++;
            else {
                System.out.println("****  "+dictPath);
                empty++;
            };



        }
        System.out.println("folder num :" + files+" empty size "+ empty +" success " +success+" equal "+equal + " timeout "+timeout + " extra " + extra +
                " erroIO "+ errorIO + " hermitError " + hermitError +" runtimeerror "+ runtimeerror);
    }
    public static void main(String[] args)throws Exception{


        //testDefinedConceptsNums();
        //testAAAI22();
        staticalAAAI22();
        //testUI("PARTII");

        //testGhadah();
        //relationships();
        //statisticsBio();
        //String dictPath = "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/";
        //String dictPath = "/Users/liuzhao/Desktop/experiments/Test_data_for_forgetting/TestData/Corpus_2/";
        //String dictPath = "/Users/liuzhao/nju/NCBO/data/Part_Ⅵ/";
        //List<OWLOntology>ans = test3(dictPath,"ontology_202001.owl","ontology_201907.owl");
        //OWLOntology onto1 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(dictPath+"ontology_201707.owl"));
        //OWLOntology onto2 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(dictPath+"ontology_201801.owl"));
        //OWLOntology ui = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(dictPath+"0170701801.owl"));
        //OWLOntology witness = checkWitness(ans.get(0),ans.get(1),ans.get(2),"/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/log.txt",
        //        "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/20011907");
        //test2(dictPath);
        //test4("corpus2");
        //List<OWLOntology>ans = test3(dictPath,"ontology_202001.owl","ontology_201907.owl");
        //OWLOntology onto1 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(dictPath+"ontology_201707.owl"));
        //OWLOntology onto2 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(dictPath+"ontology_201801.owl"));
        //OWLOntology witness = checkWitness(ans.get(0),ans.get(1),ans.get(2),"/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/log.txt",
        //        "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/20011907");
        System.out.println("done!");
    }

}
