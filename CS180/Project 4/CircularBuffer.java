/**
 * Created by Ryan on 11/4/2015.
 */
public class CircularBuffer {
    int size;
    int messages;   //overflows after 9999
    boolean messageOverflow = false;
    String[] buffer;
    int latest;     //Also kinda acts as a message counter
    public CircularBuffer(int size) {
        this.size = size;
        this.messages = 0;
        buffer = new String[size];
        latest = -1;
    }
    public void put(String message) {
        //handle messages count overflow
        if (messages == 10000) {
            messages = 0;
            messageOverflow = true;
        }
        String actual = SuccessMessages.messageNumber(messages) + message;
        //handle circular buffer
        if (latest == (size - 1)) {
            latest = -1;
        }
        buffer[latest+1] = actual;
        latest++;
        messages++;
    }
    public int getLatest() {
        return this.latest;
    }
    public String[] getNewest(int numMessages) {
        //cannot return more messages than the size of the buffer
        if (numMessages > size) numMessages = size;
        //
        if (latest == -1) {
            System.out.println("No messages have been added yet");
            //return null;
        }
        if (numMessages < 0) {
            System.out.println("Invalid getNewest(), returning null");
            return null;
        }
        if (numMessages == 0) {
            //Special case, return empty array
            return new String[0];
        }
        if (numMessages > 0) {
            //EX: 6 messages in a size 6 buffer
            if ((messages  <= buffer.length) && !messageOverflow) {
                System.out.println("Condition 1");
                if (numMessages > messages) {
                    //Retrieve only the messages in the buffer
                    System.out.println("Buffer not full");
                    numMessages = messages;
                }
                String[] tmpBuffer = new String[numMessages];
                for (int i = latest; i > latest - numMessages; i--) {
                    int modI = Math.abs(i - (latest));
                    tmpBuffer[modI] = buffer[i];
                }
                return tmpBuffer;
            }
            //circular buffer has not been filled up yet
            //only a couple of messages in it
            /*else if ((messages < buffer.length) && !messageOverflow) {
                System.out.println("Condition 2");
                String[] tmpBuffer = new String[numMessages];
                for (int i = latest; i > latest - numMessages; i--) {
                    int modI = Math.abs(i - (latest));
                    tmpBuffer[modI] = buffer[i];
                }
                return tmpBuffer;
            }*/
            //buffer has rolled over
            //else if ((messages > buffer.length) && !messageOverflow) {
            else {
                System.out.println("Condition 2");
                //Two loops, one from latest to x, other from buffer.length to y
                System.out.println("Latest: " + latest);
                int x = latest - (numMessages - 1);
                System.out.println("X: " + x);

                String[] tmpBuffer = new String[numMessages];
                int tmpBufferlatest = 000;
                if (x >= 0) {
                    //Only have to do one loop
                    for (int i = latest; i > (x - 1); i--) {
                        int modI = Math.abs(i - latest);
                        tmpBuffer[modI] = buffer[i];
                    }
                }
                    if (x < 0) {
                        //Have to do two loops
                        for (int i = latest; i > -1; i--) {
                            int modI = Math.abs(i - latest);
                            tmpBuffer[modI] = buffer[i];
                            tmpBufferlatest++;
                        }
                        //Do second loop
                        int travelto = (size - 1) - Math.abs(x);
                        for (int i = (size - 1); i > travelto; i--) {
                            tmpBuffer[tmpBufferlatest] = buffer[i];
                            tmpBufferlatest++;
                        }
                    }
                    return tmpBuffer;
                }
                //buffer has rolled over and so has messages
                /*else {
                    System.out.println("Condition 3");
                }*/
            }
        return null;
    }
}
