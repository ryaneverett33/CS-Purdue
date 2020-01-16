package apps.trafficIsolation;
public class Host {
    public String address;      //00:00:00:00:00:01/None
    public String name;         //h1
    public int tenant;          //1

    public Host(String address, String name, int tenant) {
        this.address = address;
        this.name = name;
        this.tenant = tenant;
    }
}