package com.el.dg;

import com.sun.deploy.net.proxy.PACFunctionsImpl;
import de.tudresden.inf.lat.jcel.coreontology.axiom.*;
import de.tudresden.inf.lat.jcel.owlapi.main.JcelReasoner;
import de.tudresden.inf.lat.jcel.owlapi.translator.TranslationRepository;
import de.tudresden.inf.lat.jcel.reasoner.main.RuleBasedReasoner;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import sun.dc.path.PathError;
import sun.tools.jconsole.MaximizableInternalFrame;
import utils.LOG;

import java.io.FileNotFoundException;
import java.nio.channels.NonReadableChannelException;
import java.nio.channels.SelectableChannel;
import java.sql.*;
import java.util.*;

/**
 * Created by winter on 28/8/15.
 */
public class PatternGeneration {
    private Set<NormalizedIntegerAxiom> tbox;
    private Set<NormalizedIntegerAxiom> tboxCP;
    private OWLOntology ontology;

    private Set<Set<NormalizedIntegerAxiom>> S;
    private Set<Set<NormalizedIntegerAxiom>> S_v;
    private Set<Set<NormalizedIntegerAxiom>> S_a;

    private Map<Integer, OWLClass> classMap;
    private Map<Integer, OWLObjectProperty> propMap;

    private Map<Set<Set<NormalizedIntegerAxiom>>, PatternInfo> infoMap;

    public static final String url = "jdbc:mysql://localhost/eldg";
    public static final String user = "root";
    public static final String password = "1";
    public static final String driver = "com.mysql.jdbc.Driver";

    private Connection dbConnection;

    final public static Map<String, Integer> axiomTypeMap = new HashMap<String, Integer>(){{
            put(GCI0Axiom.class.toString(), 1);
            put(GCI1Axiom.class.toString(), 2);
            put(GCI2Axiom.class.toString(), 3);
            put(GCI3Axiom.class.toString(), 4);
            put(RI2Axiom.class.toString(), 5);
            put(RI3Axiom.class.toString(), 6);
    }};

    final public static List<String> columnName = new ArrayList<String>(){{
        add("fnode");
        add("tnode");
        add(null);
        add("fir_node");
        add("sec_node");
        add("third_node");
    }};

    public PatternGeneration(OWLOntology ont) throws SQLException {
        dbConnection = DriverManager.getConnection(url, user, password);
        dbConnection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
        Statement stmt = dbConnection.createStatement();
        stmt.execute("set session read_buffer_size=41943040"); // 40M
        stmt.execute("set session read_rnd_buffer_size=41943040"); // 40M
        stmt.execute("set session sort_buffer_size=167772160"); // 160M
        stmt.execute("set session join_buffer_size=167772160"); // 160M
        stmt.close();
        if (!dbConnection.getAutoCommit())
            dbConnection.commit();

        ontology = ont;

    }

    public void doGenerate() throws FileNotFoundException, SQLException, ClassNotFoundException {
        doPretreatment();


        /* Pattern generation algorithm begin */
        Set<NormalizedIntegerAxiom> diffPattern = a_patternInSetDifference(S_a, S_v);

        while (diffPattern != null){
            Set<NormalizedIntegerAxiom> g = diffPattern;

            /* TBD */
            //S_a.remove(g);

            addPattern(S_v, g, false);

            if (findSubstitution(g, false))
                addPattern(S, g, false);

            if (findSubstitution(g, true)){
                addPattern(S_a, g, true);

//                Iterator<NormalizedIntegerAxiom> gIterator = g.iterator();
//
//                while (gIterator.hasNext()){
//                    NormalizedIntegerAxiom axiom = gIterator.next();

                Set<Set<NormalizedIntegerAxiom>> candidatePattern = getCandidatePattern(g);

                Iterator<Set<NormalizedIntegerAxiom>> candiIterator = candidatePattern.iterator();

                while (candiIterator.hasNext())
                    addPattern(S_a, candiIterator.next(), true);

            }


            diffPattern = a_patternInSetDifference(S_a, S_v);
        }
    }

    private Set<Integer> getSignature(Set<NormalizedIntegerAxiom> pattern){
        Set<Integer> signature = new HashSet<Integer>();

        Iterator<NormalizedIntegerAxiom> iterator = pattern.iterator();
        while (iterator.hasNext()){
            NormalizedIntegerAxiom axiom = iterator.next();

            signature.addAll(axiom.getClassesInSignature());
            signature.addAll(axiom.getObjectPropertiesInSignature());
        }
        return signature;
    }

    private Integer getMaxId(Set<Integer> idCollection){
        Iterator<Integer> iterator = idCollection.iterator();
        Integer res = 0;

        while (iterator.hasNext()){
            Integer id = iterator.next();

            if (id > res)
                res = id;
        }

        return res;
    }

    private Set<Set<NormalizedIntegerAxiom>> getCandidatePattern(Set<NormalizedIntegerAxiom> gSet){
        Set<Integer> signature = getSignature(gSet);
        Iterator<Integer> integerIterator = signature.iterator();
        int max = 0;
        while (integerIterator.hasNext()){
            Integer tmp = integerIterator.next();

            if (tmp > max)
                max = tmp;
        }

        Set<Set<NormalizedIntegerAxiom>> candidateSet = new HashSet<Set<NormalizedIntegerAxiom>>();
        Iterator<NormalizedIntegerAxiom> nit = gSet.iterator();

        while (nit.hasNext()){
            NormalizedIntegerAxiom tmpAxiom = nit.next();

            Integer axiomType = PatternGeneration.axiomTypeMap.get(tmpAxiom.getClass().toString());

            if (axiomType != PatternGeneration.axiomTypeMap.get(GCI0Axiom.class.toString())
                    && axiomType != PatternGeneration.axiomTypeMap.get(GCI2Axiom.class.toString()))
                continue;
            else{
                Set<Set<NormalizedIntegerAxiom>> bodyPart = getRuleBody(tmpAxiom, max);

                Iterator<Set<NormalizedIntegerAxiom>> bodyPartIt = bodyPart.iterator();
                while (bodyPartIt.hasNext()){
                    Set<NormalizedIntegerAxiom> replacePart = bodyPartIt.next();

                    Set<NormalizedIntegerAxiom> replaceAxiomSet = new HashSet<NormalizedIntegerAxiom>();
                    replaceAxiomSet.addAll(gSet);
                    replaceAxiomSet.remove(tmpAxiom);
                    replaceAxiomSet.addAll(replacePart);

                    candidateSet.add(replaceAxiomSet);
                }
            }


        }

        return candidateSet;
    }

    /* replace rule.head with rule.body */
    private Set<Set<NormalizedIntegerAxiom>> getRuleBody(NormalizedIntegerAxiom axiom,  int maxId){
        NormalizedIntegerAxiomFactoryImpl fat = new NormalizedIntegerAxiomFactoryImpl();
        Set<Set<NormalizedIntegerAxiom>> bodyPart = new HashSet<Set<NormalizedIntegerAxiom>>();

        if (axiom instanceof GCI0Axiom){
            GCI0Axiom tmpAxiom = (GCI0Axiom) axiom;

            Set<NormalizedIntegerAxiom> cp1 = new HashSet<NormalizedIntegerAxiom>();
            cp1.add(fat.createGCI0Axiom(tmpAxiom.getSubClass(), maxId+1));
            cp1.add(fat.createGCI0Axiom(maxId+1, tmpAxiom.getSuperClass()));
            bodyPart.add(cp1);

            Set<NormalizedIntegerAxiom> cp2 = new HashSet<NormalizedIntegerAxiom>();
            cp2.add(fat.createGCI0Axiom(tmpAxiom.getSubClass(), maxId+1));
            cp2.add(fat.createGCI0Axiom(tmpAxiom.getSubClass(), maxId + 2));
            cp2.add(fat.createGCI1Axiom(maxId + 1, maxId + 2, tmpAxiom.getSuperClass()));
            bodyPart.add(cp2);

            Set<NormalizedIntegerAxiom> cp3 = new HashSet<NormalizedIntegerAxiom>();
            cp3.add(fat.createGCI0Axiom(tmpAxiom.getSubClass(), maxId + 1));
            cp3.add(fat.createGCI1Axiom(tmpAxiom.getSubClass(), maxId + 1, tmpAxiom.getSuperClass()));
            bodyPart.add(cp3);

            Set<NormalizedIntegerAxiom> cp4 = new HashSet<NormalizedIntegerAxiom>();
            cp4.add(fat.createGCI0Axiom(tmpAxiom.getSubClass(), maxId + 1));
            cp4.add(fat.createGCI1Axiom(maxId + 1, tmpAxiom.getSubClass(), tmpAxiom.getSuperClass()));
            bodyPart.add(cp4);

            Set<NormalizedIntegerAxiom> cp5 = new HashSet<NormalizedIntegerAxiom>();
            cp5.add(fat.createGCI2Axiom(tmpAxiom.getSubClass(), maxId + 1, maxId + 2));
            cp5.add(fat.createGCI0Axiom(maxId + 2, maxId + 3));
            cp5.add(fat.createGCI3Axiom(maxId + 1, maxId + 3, tmpAxiom.getSubClass()));
            bodyPart.add(cp5);

            Set<NormalizedIntegerAxiom> cp6 = new HashSet<NormalizedIntegerAxiom>();
            cp6.add(fat.createGCI2Axiom(tmpAxiom.getSubClass(), maxId+1, maxId+2));
            cp6.add(fat.createGCI3Axiom(maxId+1, maxId+2, tmpAxiom.getSuperClass()));
            bodyPart.add(cp6);

        }else{
            GCI2Axiom tmpAxiom = (GCI2Axiom) axiom;

            Set<NormalizedIntegerAxiom> cp7 = new HashSet<NormalizedIntegerAxiom>();
            cp7.add(fat.createGCI2Axiom(tmpAxiom.getSubClass(), maxId + 1, tmpAxiom.getClassInSuperClass()));
            cp7.add(fat.createRI2Axiom(maxId + 1, tmpAxiom.getPropertyInSuperClass()));
            bodyPart.add(cp7);

            Set<NormalizedIntegerAxiom> cp8 = new HashSet<NormalizedIntegerAxiom>();
            cp8.add(fat.createGCI2Axiom(tmpAxiom.getSubClass(), maxId+1, maxId+2));
            cp8.add(fat.createGCI2Axiom(maxId+2, maxId+3, tmpAxiom.getClassInSuperClass()));
            cp8.add(fat.createRI3Axiom(maxId + 1, maxId + 3, tmpAxiom.getPropertyInSuperClass()));
            bodyPart.add(cp8);

        }

        return bodyPart;
    }

    private void addPattern(Set<Set<NormalizedIntegerAxiom>> patternSet, Set<NormalizedIntegerAxiom> pattern, boolean checkVariant){
        if (!checkVariant){
            patternSet.add(pattern);
            return;
        }

        Iterator<Set<NormalizedIntegerAxiom>> psIt = patternSet.iterator();
        while (psIt.hasNext()){
            Set<NormalizedIntegerAxiom> tmpPattern = psIt.next();
            if (isPatternEqual(tmpPattern, pattern))
                return;
        }

        patternSet.add(pattern);
    }

    /* normalize and get class, property map*/

    private void doPretreatment() throws FileNotFoundException, SQLException, ClassNotFoundException {
        JcelReasoner reasoner = new JcelReasoner(ontology, false);
        RuleBasedReasoner ruleBasedReasoner = (RuleBasedReasoner) reasoner.getReasoner();

        TranslationRepository translatorReposity = reasoner.getTranslator().getTranslationRepository();
        classMap = translatorReposity.getClassMap();
        propMap = translatorReposity.getObjectPropertyMap();
        tbox = ruleBasedReasoner.getNormalizedIntegerAxiomSet();

        TBoxCP tcp = new TBoxCP(dbConnection, tbox);
        tcp.generate();
    }

    public Set<NormalizedIntegerAxiom> a_patternInSetDifference(Set<Set<NormalizedIntegerAxiom>> Sa, Set<Set<NormalizedIntegerAxiom>> Sv){
        Iterator<Set<NormalizedIntegerAxiom>> saIt = Sa.iterator();

        while (saIt.hasNext()){
            Set<NormalizedIntegerAxiom> tmpSaPat = saIt.next();

            Iterator<Set<NormalizedIntegerAxiom>> svIt = Sv.iterator();
            boolean flag = true;

            while (svIt.hasNext()){
                Set<NormalizedIntegerAxiom> tmpSvPat = svIt.next();

                if (isPatternEqual(tmpSaPat, tmpSvPat)) {
                    flag = false;
                    break;
                }
            }

            if (flag){
                return tmpSaPat;
            }
        }

        return null;
    }

    private boolean findSubstitution(Set<NormalizedIntegerAxiom> g, boolean isTboxCp) throws SQLException {
        Statement stmt = dbConnection.createStatement();
        String sql = compseSQL(g, isTboxCp);

        ResultSet rt = stmt.executeQuery(sql);

        return rt.next();
    }

    public Set<Set<NormalizedIntegerAxiom>> getPatterns(){
        return S;
    }

    private boolean isPatternEqual(Set<NormalizedIntegerAxiom> pa, Set<NormalizedIntegerAxiom> pb){

        if (pa.size() != pb.size())
            return false;

        Set<Integer> paCPSignature = getSignature(pa);
        Set<Integer> pbCPSignature = getSignature(pb);

        if (paCPSignature.size() != pbCPSignature.size())
            return false;

        PatternInfo paInfo = getPatternInfo(pa);
        PatternInfo pbInfo = getPatternInfo(pb);

        return paInfo.isEqual(pbInfo);
    }

    private String compseSQL(Set<NormalizedIntegerAxiom> pattern, boolean isTboxCp){
        if (pattern == null)
            return null;

        String sqlstmt = "select * from ";

        String tablePrefix = "p";
        if (!isTboxCp) tablePrefix = "t" + tablePrefix;

        Map<Integer, IDInfo> equalMap = new HashMap<Integer, IDInfo>();
        Iterator<NormalizedIntegerAxiom> axiomIterator = pattern.iterator();

        Integer index = 0;
        NormalizedIntegerAxiom prevAxiom = null;

        while (axiomIterator.hasNext()){
            NormalizedIntegerAxiom tmpAxiom = axiomIterator.next();

            Integer[] iris = getIRIs(tmpAxiom);


            Integer axiomTypeInt = PatternGeneration.axiomTypeMap.get(tmpAxiom.getClass().toString());

            String tableStr = tablePrefix + axiomTypeInt;

            String tmpTableStr = "h" + index.toString();

            if (index == 0){
                sqlstmt += tableStr + " " + tmpTableStr + " ";
            }else{
                String joinStmt = "inner join ";
                sqlstmt += joinStmt + tableStr + " " + tmpTableStr + " on ";

                for (int i = 0; i<iris.length; i++){
                    if (equalMap.keySet().contains(iris[i])){

                        IDInfo info = equalMap.get(iris[i]);
                        String eqLeft = "h" + info.index.toString() + "." + info.column + "=";

                        //TODO add column name

                        String eqRight = tmpTableStr + "." + PatternGeneration.columnName.get((iris.length-2)*3+i) + " ";

                        if (i != 0)
                            sqlstmt += "and ";

                        sqlstmt += eqLeft + eqRight + " ";

                        if (PatternGeneration.axiomTypeMap.get(tmpAxiom.getClass().toString())
                                == info.axiomType && index != info.index){
                            sqlstmt += "and " + "h" + index + ".id<>" + info.index + ".id ";
                        }


                    }else{
                        /* store the first */
                        equalMap.put(iris[i], new IDInfo(PatternGeneration.columnName.get((iris.length-2)*3+i), index,
                                PatternGeneration.axiomTypeMap.get(tmpAxiom.getClass().toString())));
                    }
                }




//            for (int i = 0; i<iris.length; i++){
//                if (!equalMap.keySet().contains(iris[i])){
//
//                    /* store the first */
//                    equalMap.put(iris[i], new IDInfo(PatternGeneration.columnName.get((iris.length-2)*3+i), index,
//                            PatternGeneration.axiomTypeMap.get(tmpAxiom.getClass().toString())));
//                }
            }

            prevAxiom = tmpAxiom;
            index++;
        }

        return sqlstmt;
    }

    private String getColumnName(Integer length, Integer index){
        return PatternGeneration.columnName.get((length-2)*3+index);
    }

    private PatternInfo getPatternInfo(Set<NormalizedIntegerAxiom> pattern){
        PatternInfo patternInfo = new PatternInfo();

        Iterator<NormalizedIntegerAxiom> patternIt = pattern.iterator();


        while (patternIt.hasNext()){
            NormalizedIntegerAxiom tmpAxiom = patternIt.next();

            String className = tmpAxiom.getClass().toString();
            if (patternInfo.axiomTypeCount.keySet().contains(className)){
                patternInfo.axiomTypeCount.put(className, patternInfo.axiomTypeCount.get(className)+1);
            }else{
                patternInfo.axiomTypeCount.put(className, 1);
            }

            if (patternInfo.iriCount.keySet().contains(className)){
                patternInfo.iriCount.get(className).addAll(tmpAxiom.getClassesInSignature());
                patternInfo.iriCount.get(className).addAll(tmpAxiom.getObjectPropertiesInSignature());
            }else{
                patternInfo.iriCount.put(className, tmpAxiom.getClassesInSignature());
                patternInfo.iriCount.get(className).addAll(tmpAxiom.getObjectPropertiesInSignature());
            }
        }

        return patternInfo;
    }

    private Integer[] getIRIs(NormalizedIntegerAxiom axiom){
        if (axiom instanceof GCI0Axiom){
            GCI0Axiom tmpAxiom = (GCI0Axiom) axiom;
            Integer[] iris = new Integer[2];
            iris[0] = tmpAxiom.getSubClass();
            iris[1] = tmpAxiom.getSuperClass();
            return iris;
        }else if (axiom instanceof GCI1Axiom){
            GCI1Axiom tmpAxiom = (GCI1Axiom) axiom;
            Integer[] iris = new Integer[3];
            iris[0] = tmpAxiom.getLeftSubClass();
            iris[1] = tmpAxiom.getRightSubClass();
            iris[2] = tmpAxiom.getSuperClass();
            return iris;
        }else if (axiom instanceof GCI2Axiom){
            GCI2Axiom tmpAxiom = (GCI2Axiom) axiom;
            Integer[] iris = new Integer[3];
            iris[0] = tmpAxiom.getSubClass();
            iris[1] = tmpAxiom.getPropertyInSuperClass();
            iris[2] = tmpAxiom.getClassInSuperClass();
            return iris;
        }else if (axiom instanceof GCI3Axiom){
            GCI3Axiom tmpAxiom = (GCI3Axiom) axiom;
            Integer[] iris = new Integer[3];
            iris[0] = tmpAxiom.getPropertyInSubClass();
            iris[1] = tmpAxiom.getClassInSubClass();
            iris[2] = tmpAxiom.getSuperClass();
            return iris;
        }else if (axiom instanceof RI2Axiom){
            RI2Axiom tmpAxiom = (RI2Axiom) axiom;
            Integer[] iris = new Integer[2];
            iris[0] = tmpAxiom.getSubProperty();
            iris[1] = tmpAxiom.getSuperProperty();
            return iris;
        }else if (axiom instanceof RI3Axiom){
            RI3Axiom tmpAxiom = (RI3Axiom) axiom;
            Integer[] iris = new Integer[3];
            iris[0] = tmpAxiom.getLeftSubProperty();
            iris[1] = tmpAxiom.getRightSubProperty();
            iris[2] = tmpAxiom.getSuperProperty();
            return iris;
        }else{
            LOG.info("WTF! " + axiom.toString());
            return null;
        }

    }
}
 class IDInfo{
     public String column;
     public Integer index;
     public Integer axiomType;

     public IDInfo(String col, Integer idx, Integer type){
         column = col;
         index = idx;
         axiomType = type;
     }
 };

