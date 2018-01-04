/**
 * Created by Ryan on 11/6/2015.
 */
public class SuccessMessages {
    //Created as to not fuck with the MessageFactory class
    public static String makeGeneric() {
        return "SUCCESS\r\n";
    }
    public static String makeLogin(int cookie) {
        //it doesn't need to be a long, 32 bits is plenty!
        //Leading zero credits goes to:
        //http://stackoverflow.com/questions/4051887/how-to-format-a-java-string-with-leading-zero
        String cook = String.format("%04d",cookie);
        //return "\"SUCCESS\n"+cook+"\n\"";
        return "SUCCESS\t"+cook+"\r\n";
    }
    public static String messageNumber(int number) {
        return String.format("%04d",number) +") ";
    }
    public static String makeMessages(String[] messages) {
        String base = "SUCCESS\t";
        String end = "\r\n";
        String body = "";
        for (int i = 0; i < messages.length; i++) {
            String text;
            try {
                text = messages[i];
            }
            catch (Exception e) {
                return "BADFAIL";
            }
            if (!(i == (messages.length - 1))) {
                text = text.concat("\t");
            }
            body = body.concat(text);
        }
        return base+body+end;
    }
}
