import java.io.*;
import java.util.*;

/**
 * Created by Ryan on 12/2/2015.
 */
public class Stats {
    public static HashMap<String, Integer> wins(String filename) {
        File f = null;
        BufferedReader br;
        HashMap<String, Integer> data = new HashMap<>();

        try {
            f = new File(filename);
        }
        catch (Exception e) {
            System.out.println("Unable to create File");
            return null;
        }
        try {
            br = new BufferedReader(new FileReader(f));
        }
        catch (Exception e) {
            System.out.println("Unable to create BufferedReader");
            return null;
        }
        boolean canContinue = true;
        do {
            String line = null;
            try {
                line = br.readLine();
            }
            catch (Exception e) {
                canContinue = false;
            }
            if (canContinue) {
                if (line == null || line.length() == 0) {
                    //Found last line, kill
                    canContinue = false;
                    break;
                }
                //System.out.println(line);     //Debug to show line data
                //Handle line data
                String[] info = line.split(" ");
                boolean gameWon = false;    //Check if first team one, else second team did
                if (info[0].equals("0")) {
                    gameWon = true;
                }
                boolean firstTeam = true;   //Set to false when we hit "vs."
                for (int i = 1; i < info.length; i++) {
                    if (gameWon) {
                        // it's 5v5, but let's ignore that
                        // First team won
                        if (info[i].equals("vs.")) {
                            firstTeam = false;  //defines when we've reached the second team
                        }
                        else {
                            if (firstTeam) {
                                String player = info[i];
                                if (data.containsKey(player)) {
                                    //If the player exists, add data
                                    int initial = data.get(player);
                                    //Update score with an additional win
                                    data.replace(player,initial+1);
                                }
                                else {
                                    //Player doesn't exist, create player and add their score
                                    data.put(player,1);
                                }
                            }
                            else {
                                //players lost, so add 0 as their score if they don't exist
                                String player = info[i];
                                if (!data.containsKey(player)) {
                                    //Add the player if they don't exist with their score
                                    data.put(player,0);
                                }
                            }
                        }
                    }
                    else {
                        // it's 5v5, but let's ignore that
                        // Second team won
                        if (info[i].equals("vs.")) {
                            firstTeam = false;  //defines when we've reached the second team
                        }
                        else {
                            if (firstTeam) {
                                //First team lost
                                String player = info[i];
                                if (!data.containsKey(player)) {
                                    //If the player doesn't already exist, add them
                                    data.put(player,0); //They lost, so set score to 0.
                                }
                            }
                            else {
                                String player = info[i];
                                if (data.containsKey(player)) {
                                    //If the player exists, add data
                                    int initial = data.get(player);
                                    //Update score with an additional win
                                    data.replace(player,initial+1);
                                }
                                else {
                                    //Player doesn't exist, create player and add their score
                                    data.put(player,1);
                                }
                            }
                        }
                    }
                }
            }
        }
        while (canContinue);
        data = data;
        return data;
    }
    public static String winner(String filename) {
        //Assuming winner() always wins(), so we require the filename as an argument to pass to wins()
        HashMap<String,Integer> data = wins(filename);
        //http://stackoverflow.com/questions/10462819/get-keys-from-hashmap-in-java
        //use keySet()
        int largest = Integer.MIN_VALUE;    //temporary value
        String player = null;
        for (String s : data.keySet()) {
            int value = data.get(s);
            if (value > largest) {
                largest = value;
                player = s;
            }
        }
        if (largest == Integer.MIN_VALUE) {
            return "No data";
        }
        return player;
    }
}
