package utils;

import java.io.Serializable;

public class LOG {
	public static boolean flag = false;
	public static void info(Serializable inf){
		if (flag) {
			StackTraceElement ste = new Throwable().getStackTrace()[1];
	        String tmpStr = "[" + ste.getFileName() + ", Line " + ste.getLineNumber() + "]: ";
			System.out.println(tmpStr+inf.toString());
		}
		
	}
}
