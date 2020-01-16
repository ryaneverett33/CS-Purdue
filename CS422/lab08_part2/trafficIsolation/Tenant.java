package apps.trafficIsolation;
import java.util.ArrayList;

public class Tenant {
    public int id;
    public ArrayList<Host> hosts;
    TrafficType trafficAssignment;
    public Tenant(int id) {
        this.id = id;
        this.hosts = new ArrayList();
    }
    public boolean addHost(Host host) {
        return this.hosts.add(host);
    }
    public void addTraffic(TrafficType type) {
        this.trafficAssignment = type;
    }
    public static TrafficType parseType(String s) throws Exception {
        if (s.toUpperCase().equals("WEB"))
            return TrafficType.WEB;
        else if (s.toUpperCase().equals("ICMP"))
            return TrafficType.ICMP;
        else if (s.toUpperCase().equals("VIDEO_STREAMING"))
            return TrafficType.VIDEO_STREAMING;
        else
            throw new Exception("Invalid Traffic Type");
    }
    public void printDebug() {
        System.out.println(String.format("Tenant: %d, Host Count: %d, Traffic Assignment: %s", id, hosts.size(), trafficAssignment));
    }
    public enum TrafficType {
        WEB,
        ICMP,
        VIDEO_STREAMING
    }
    public boolean containsHost(String hostID) {
        for (Host host : hosts) {
            if (host.address.equals(hostID))
                return true;
        }
        return false;
    }
    public static Tenant getTenantFromHost(Tenant[] tenants, String hostID) throws Exception {
        if (tenants == null) {
            throw new Exception("Unable to get Tenant from Host, tenants[] is null");
        }
        for (Tenant tenant : tenants) {
            if (tenant.containsHost(hostID))
                return tenant;
        }
        return null;
    }
}