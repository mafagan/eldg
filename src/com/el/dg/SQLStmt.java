package com.el.dg;

/**
 * Created by winter on 25/8/15.
 */
public class SQLStmt {
    public static String CR_1 = "select distinct b0.fnode, b1.tnode, h0.id from p1 b0 inner join p1 b1 on b0.tnode=b1.fnode left join p1 h0 on b0.fnode=h0.fnode and b1.tnode=h0.tnode";

    public static String CR_2 = "select distinct b0.fnode, b2.third_node, h0.id from p1 b0 inner join p1 b1 on b0.fnode=b1.fnode and b0.tnode<>b1.tnode inner join p3 b2 on b0.tnode=b2.fir_node and b1.tnode=b2.sec_node left join p1 h0 on h0.fnode=b0.fnode and h0.tnode=b2.third_node;";

    public static String CR_3 = "select b0.fnode, b1.third_node, h0.id from p1 b0 inner join p2 b1 on b0.fnode=b1.fir_node and b0.tnode=b1.sec_node left join p1 h0 on b0.fnode=h0.fnode and b1.third_node=h0.tnode";

    public static String CR_4 = "select b0.fnode, b1.third_node, h0.id from p1 b0 inner join p2 b1 on b0.fnode=b1.sec_node and b0.tnode=b1.fir_node left join p1 h0 on b0.fnode=h0.fnode and b1.third_node=h0.tnode";

    public static String CR_5 = "select distinct b0.fir_node, b2.third_node, h0.id from p3 b0 inner join p1 b1 on b0.third_node=b1.fnode inner join p4 b2 on b0.sec_node=b2.fir_node and b1.tnode=b2.sec_node left join p1 h0 on b0.fir_node=h0.fnode and b2.third_node=h0.tnode";

    public static String CR_6 = "select b0.fir_node, b1.third_node, h0.id from p3 b0 inner join p4 b1 on b0.sec_node=b1.fir_node and b0.third_node=b1.sec_node left join p1 h0 on h0.fnode=b0.fir_node and h0.tnode=b1.third_node";

    public static String CR_7 = "select distinct b0.fir_node, b1.tnode, b0.third_node, h0.id from p3 b0 inner join p5 b1 on b0.sec_node=b1.fnode left join p3 h0 on b0.fir_node=h0.fir_node and b1.tnode=h0.sec_node and b0.third_node=h0.third_node;";

    public static String CR_8 = "select distinct b0.fir_node, b1.third_node, b2.third_node from p3 b0 inner join p6 b1 on b0.sec_node=b1.fir_node inner join p3 b2 on b1.sec_node=b2.sec_node and b0.third_node=b2.fir_node left join p3 h0 on b0.fir_node=h0.fir_node and b1.third_node=h0.sec_node and b0.third_node=h0.third_node;";

//    public static String CR_1 = "select distinct b0.fnode, b1.tnode, h0.id from p1 b0 cross join p1 b1 on b0.tnode=b1.fnode left join p1 h0 on b0.fnode=h0.fnode and b1.tnode=h0.tnode";
//    public static String CR_2 = "select distinct b0.fir_node, b0.sec_node, b1.tnode, h0.id from p4 b0 cross join p1 b1 on b0.third_node=b1.fnode left join p4 h0 on b0.fir_node=h0.fir_node and b0.sec_node=h0.sec_node and b1.tnode=h0.third_node";
//    public static String CR_3 = "select distinct b0.fnode, b1.sec_node, b1.third_node, h0.id from p1 b0 cross join p3 b1 on b0.tnode=b1.fir_node left join p3 h0 on b0.fnode=h0.fir_node and b1.sec_node=h0.sec_node and b1.third_node=h0.third_node";
//    public static String CR_4 = "select distinct b0.fnode, b2.third_node, h0.id from p1 b0 cross join p1 b1 on b0.fnode=b1.fnode and b0.tnode<>b1.tnode inner join p3 b2 on b0.tnode=b2.fir_node and b1.tnode=b2.sec_node left join p1 h0 on h0.fnode=b0.fnode and h0.tnode=b2.third_node;";
//    public static String CR_5 = "select distinct b0.fir_node, b0.sec_node, b2.third_node, h0.id from p4 b0 cross join p4 b1 on b0.fir_node=b1.fir_node and b0.sec_node=b1.sec_node and b0.third_node<>b1.third_node inner join p2 b2 on b0.third_node=b2.fir_node and b1.third_node=b2.sec_node left join p4 h0 on b0.fir_node=h0.fir_node and b0.sec_node=h0.sec_node and b2.third_node=h0.third_node;";
//    public static String CR_6 = "select distinct b0.fir_node, b2.third_node, h0.id from p3 b0 inner join p1 b1 on b0.third_node=b1.fnode inner join p4 b2 on b0.sec_node=b2.fir_node and b1.tnode=b2.sec_node left join p1 h0 on b0.fir_node=h0.fnode and b2.third_node=h0.tnode";
//    public static String CR_7 = "select distinct b0.fir_node, b1.tnode, b0.third_node, h0.id from p3 b0 inner join p5 b1 on b0.sec_node=b1.fnode left join p3 h0 on b0.fir_node=h0.fir_node and b1.tnode=h0.sec_node and b0.third_node=h0.third_node;";
//    public static String CR_8 = "select distinct b0.fir_node, b1.third_node, b2.third_node from p3 b0 inner join p6 b1 on b0.sec_node=b1.fir_node inner join p3 b2 on b1.sec_node=b2.sec_node and b0.third_node=b2.fir_node left join p3 h0 on b0.fir_node=h0.fir_node and b1.third_node=h0.sec_node and b0.third_node=h0.third_node;";
//    public static String CR_9 = "select distinct b0.fnode, b1.tnode, h0.id from p5 b0 cross join p5 b1 on b0.tnode=b1.fnode left join p5 h0 on b0.fnode=h0.fnode and b1.tnode=h0.tnode";
//    public static String CR_10 = "select distinct b1.fnode, b0.sec_node, b0.third_node, h0.id from p6 b0 inner join p5 b1 on b0.fir_node=b1.tnode left join p6 h0 on b1.fnode=h0.fir_node and b0.sec_node=h0.sec_node and b0.third_node=h0.third_node;";
//    public static String CR_11 = "select distinct b0.fir_node, b0.sec_node, b1.tnode, h0.id from p6 b0 inner join p5 b1 on b0.third_node=b1.fnode left join p6 h0 on b0.fir_node=h0.fir_node and b0.sec_node=h0.sec_node and b1.tnode=h0.third_node;";
//    public static String CR_12 = "select distinct b1.fnode, b0.sec_node, b0.third_node, h0.id from p6 b0 inner join p5 b1 on b0.sec_node=b1.tnode left join p6 h0 on b0.fir_node=h0.fir_node and b1.fnode=h0.sec_node and b0.third_node=h0.third_node;";

    public static String[] rules = {CR_1, CR_2, CR_3, CR_4, CR_5, CR_6, CR_7, CR_8};
    public static int[] entailmentPNum = {1, 1, 1, 1, 3, 3};

}
