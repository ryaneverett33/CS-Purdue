package apps.trafficIsolation;
import org.apache.log4j.Logger;
import java.io.*;
import java.util.*;

import api.flowservice.Flow;
import api.flowservice.FlowAction;
import api.flowservice.FlowActionType;
import api.flowservice.FlowMatch;
import api.topostore.TopoEdge;
import api.topostore.TopoEdgeType;
import api.topostore.TopoHost;
import config.ConfigService;
import drivers.controller.Controller;

import apps.trafficIsolation.*;
public class TrafficIsolation{
    public static final String appRoot = "/home/osboxes/umbrella/src/main/java/apps/trafficIsolation/";
    public static final String HOST_TENANT_FILE_LOC = "host_tenant_assignments.txt";
    public static final String TENNANT_TRAFFIC_FILE_LOC = "tenant_traffic_assignments.txt";
    public static final String APP_ID = "TrafficIsolation";
    public static final int TIMEOUT = 100;
    public static final int PRIORITY = 1000;
    


    public static Logger log = Logger.getLogger(TrafficIsolation.class);
    public static String[] ReadAllLines(File f) throws Exception {
        ArrayList lines = new ArrayList();
        BufferedReader reader = new BufferedReader(new FileReader(f));
        String line = null;
        do {
            line = reader.readLine();
            if (line != null)
                lines.add(line);
        }
        while (line != null);
        reader.close();
        String[] arr = new String[lines.size()];
        lines.toArray(arr);
        return arr;
    }
    public static Tenant[] parseHostTenantAssignment(String filename) throws Exception {
        /*
            00:00:00:00:00:01/None 1
            00:00:00:00:00:02/None 2
            00:00:00:00:00:03/None 1
            00:00:00:00:00:04/None 2
            00:00:00:00:00:05/None 1
            00:00:00:00:00:06/None 2
        */
        File f = new File(filename);
        if (!f.exists() || !f.canRead()) {
            //System.out.println(String.format("File: %s\n exists: %s, canRead: %s", filename, f.exists(), f.canRead()));
            throw new FileNotFoundException("unable to read from file");
        }
        String[] lines = ReadAllLines(f);
        int hostCount = 0;
        ArrayList<Tenant> tenants = new ArrayList();
        for (String line : lines) {
            String[] split = line.split(" ");
            // <host_name> <tenant_id>
            String name = split[0];
            int id = Integer.parseInt(split[1]);
            // if contains tenant
            Tenant parentTenant = null;
            int index = -1;
            for (Tenant tenant : tenants) {
                if (tenant.id == id) {
                    index = tenants.lastIndexOf(tenant);
                    parentTenant = tenant;
                    break;
                }
            }
            if (parentTenant == null) {
                parentTenant = new Tenant(id);
                //System.out.printf("Created new tenant %d\n", id);
            }
                
           // System.out.printf("Adding host(%s, %d) to tenant %d\n", name, hostCount + 1, id);
            boolean result = parentTenant.addHost(new Host(name, Integer.toString((hostCount + 1)), id));
            //System.out.printf("Added host result %s", result);
            hostCount++;
            if (index != -1) {
                //System.out.printf("Updating tenant %d at %d\n", id, index);
                tenants.set(index, parentTenant);
            }
            else
                tenants.add(parentTenant);
        }
        Tenant[] arr = new Tenant[tenants.size()];
        tenants.toArray(arr);
        return arr;
    }
    public static Tenant[] parseTenantTrafficAssignment(String filename, Tenant[] tenants) throws Exception {
        /*
            1 WEB
            2 ICMP
            3 VIDEO_STREAMING
            4 ICMP
        */
        File f = new File(filename);
        if (!f.exists() || !f.canRead()) {
            //System.out.println(String.format("File: %s\n exists: %s, canRead: %s", filename, f.exists(), f.canRead()));
            throw new FileNotFoundException("unable to read from file");
        }
        if (tenants == null) {
            throw new Exception("Tenants argument is null");
        }
        String[] lines = ReadAllLines(f);
        Tenant[] tmpTenants = new Tenant[tenants.length];
        for (String line : lines) {
            String[] split = line.split(" ");
            // <tenant_id> <traffic_type>
            int id = Integer.parseInt(split[0]);
            int idIndex = id - 1;
            Tenant.TrafficType type = Tenant.parseType(split[1]);
            //System.out.printf("Adding type %s to tenant %d\n", type, id);
            if (idIndex < 0 || idIndex >= tenants.length) {
                //System.out.printf("Invalid id: %d, index: %d, length: %d\n", id, idIndex, tenants.length);
                throw new Exception("Invalid Tenant ID");
            }
            tmpTenants[idIndex] = tenants[idIndex];
            tmpTenants[idIndex].addTraffic(type);

        }
        return tmpTenants;
    }
    public static Flow buildFlow(FlowMatch flowMatch, FlowAction action, TopoEdge edge) {
        ArrayList<FlowAction> flowActions = new ArrayList<FlowAction>();
            flowActions.add(action);
        Flow flow = Flow.builder()
            .deviceID(edge.getSrc())
            .tableID(0)
            .flowMatch(flowMatch)
            .flowActions(flowActions)
            .priority(PRIORITY)
            .appId(APP_ID)
            .timeOut(TIMEOUT)
            .build();
        return flow;
    }
    public static FlowMatch buildICMPFlowForward(String srcMac, String dstMac, TopoHost srcHost, TopoHost dstHost) {
        FlowMatch flow = FlowMatch.builder()
            .ethSrc(srcMac)
            .ethDst(dstMac)
            .ipv4Src(srcHost.getHostIPAddresses().get(0) + "/32")
            .ipv4Dst(dstHost.getHostIPAddresses().get(0) + "/32")
            .ipProto(0x01)
            .ethType(2048)
            .icmpv4_code(0x0)
            .icmpv4_type(0x08)
            .build();
        return flow;
    }
    public static FlowMatch buildICMPFlowReverse(String srcMac, String dstMac, TopoHost srcHost, TopoHost dstHost) {
        FlowMatch flow = FlowMatch.builder()
            .ethSrc(dstMac)
            .ethDst(srcMac)
            .ipv4Src(dstHost.getHostIPAddresses().get(0) + "/32")
            .ipv4Dst(srcHost.getHostIPAddresses().get(0) + "/32")
            .ipProto(0x01)
            .ethType(2048)
            .icmpv4_code(0x0)
            .icmpv4_type(0x0)
            .build();
        return flow;
    }
    public static FlowMatch buildWebFlowForward(String srcMac, String dstMac, TopoHost srcHost, TopoHost dstHost) {
        FlowMatch flow = FlowMatch.builder()
            .ethSrc(srcMac)
            .ethDst(dstMac)
            .ipv4Src(srcHost.getHostIPAddresses().get(0) + "/32")
            .ipv4Dst(dstHost.getHostIPAddresses().get(0) + "/32")
            .ipProto(0x06)
            .ethType(2048)
            .tcpDst(80)
            .build();
        return flow;
    }
    public static FlowMatch buildWebFlowReverse(String srcMac, String dstMac, TopoHost srcHost, TopoHost dstHost) {
        FlowMatch flow = FlowMatch.builder()
            .ethSrc(dstMac)
            .ethDst(srcMac)
            .ipv4Src(dstHost.getHostIPAddresses().get(0) + "/32")
            .ipv4Dst(srcHost.getHostIPAddresses().get(0) + "/32")
            .ipProto(0x06)
            .ethType(2048)
            .tcpSrc(80)
            .build();
        return flow;
    }
    public static FlowMatch buildVideoFlowForward(String srcMac, String dstMac, TopoHost srcHost, TopoHost dstHost) {
        FlowMatch flow = FlowMatch.builder()
            .ethSrc(srcMac)
            .ethDst(dstMac)
            .ipv4Src(srcHost.getHostIPAddresses().get(0) + "/32")
            .ipv4Dst(dstHost.getHostIPAddresses().get(0) + "/32")
            .ipProto(0x06)
            .ethType(2048)
            .tcpDst(8080)
            .build();
        return flow;
    }
    public static FlowMatch buildVideoFlowReverse(String srcMac, String dstMac, TopoHost srcHost, TopoHost dstHost) {
        FlowMatch flow = FlowMatch.builder()
            .ethSrc(dstMac)
            .ethDst(srcMac)
            .ipv4Src(dstHost.getHostIPAddresses().get(0) + "/32")
            .ipv4Dst(srcHost.getHostIPAddresses().get(0) + "/32")
            .ipProto(0x06)
            .ethType(2048)
            .tcpSrc(8080)
            .build();
        return flow;
    }

    public static void main(String[] args) throws Exception {
        log.info("Traffic Isolation application\n");
        Tenant[] tenants = null;
        try {
            tenants = parseHostTenantAssignment(appRoot + HOST_TENANT_FILE_LOC);
            tenants = parseTenantTrafficAssignment(appRoot + TENNANT_TRAFFIC_FILE_LOC, tenants);
        }
        catch (Exception e) {
            System.out.println("Unable to read assignments!");
            System.out.println(e.getMessage());
            return;
        }
        String controllerName;

        Controller controller = null;
        ConfigService configService = new ConfigService();
        controllerName = configService.getControllerName();

        controller = configService.init(controllerName);

        Set<TopoHost> srchosts = controller.topoStore.getHosts();
        Set<TopoHost> dsthosts = controller.topoStore.getHosts();

        List<TopoEdge> forwardPath = null;
        List<TopoEdge> reversePath = null;
        System.out.printf("SrcHosts count: %d, dstHosts count: %d\n", srchosts.size(), dsthosts.size());
        for (TopoHost srcHost : srchosts) {
            Tenant srcTenant = Tenant.getTenantFromHost(tenants, srcHost.getHostID());
            System.out.printf("Source Tenant %d\n", srcTenant.id);
            for (TopoHost dstHost : dsthosts) {
                Tenant dstTenant = Tenant.getTenantFromHost(tenants, dstHost.getHostID());
                System.out.printf("Dest Tenant %d\n", dstTenant.id);

                if (srcTenant.id == dstTenant.id) {
                    System.out.printf("Devices belong to the same tennant %d with Traffic Rule %s\n", dstTenant.id, dstTenant.trafficAssignment);
                }
                else {
                    //System.out.printf("Devices belong to different tenants, ignoring\n");
                    continue;
                }

                String srcMac = srcHost.getHostMac();
                String dstMac = dstHost.getHostMac();
                String srcHostID = srcHost.getHostID();
                String destHostID = dstHost.getHostID();

                forwardPath = controller.topoStore.getShortestPath(srcHost.getHostID(), dstHost.getHostID());
                reversePath = controller.topoStore.getShortestPath(dstHost.getHostID(), srcHost.getHostID());

                FlowMatch forwardFlowMatch = null;
                FlowMatch reverseFlowMatch = null;
                switch (dstTenant.trafficAssignment) {
                    case ICMP:
                        System.out.printf("Adding a ICMP Flow for %s and %s\n", srcHostID, destHostID);
                        forwardFlowMatch = buildICMPFlowForward(srcMac, dstMac, srcHost, dstHost);
                        reverseFlowMatch = buildICMPFlowReverse(srcMac, dstMac, srcHost, dstHost);

                        break;
                    case WEB:
                        System.out.printf("Adding a WEB Flow for %s and %s\n", srcHostID, destHostID);
                        forwardFlowMatch = buildWebFlowForward(srcMac, dstMac, srcHost, dstHost);
                        reverseFlowMatch = buildWebFlowReverse(srcMac, dstMac, srcHost, dstHost);
                        break;
                    case VIDEO_STREAMING:
                        System.out.printf("Adding a Video Flow for %s and %s\n", srcHostID, destHostID);
                        forwardFlowMatch = buildVideoFlowForward(srcMac, dstMac, srcHost, dstHost);
                        reverseFlowMatch = buildVideoFlowReverse(srcMac, dstMac, srcHost, dstHost);
                        break;
                }


                //Allow all ICMP traffic
                //forwardFlowMatch = buildICMPFlowForward(srcMac, dstMac, srcHost, dstHost);
                //reverseFlowMatch = buildICMPFlowReverse(srcMac, dstMac, srcHost, dstHost);

                //forward path
                for (TopoEdge edge : forwardPath) {
                    if (edge.getType() == TopoEdgeType.HOST_SWITCH) {
                        continue;
                    }
                    FlowMatch flowMatch = forwardFlowMatch;

                    FlowAction flowAction = new FlowAction(FlowActionType.OUTPUT,
                            Integer.parseInt(edge.getSrcPort()));
                            
                    controller.flowService.addFlow(buildFlow(flowMatch, flowAction, edge));
                }
                //reverse path
                for (TopoEdge edge : reversePath) {
                    if (edge.getType() == TopoEdgeType.HOST_SWITCH) {
                        continue;
                    }
                    FlowMatch flowMatch = reverseFlowMatch;

                    FlowAction flowAction = new FlowAction(FlowActionType.OUTPUT,
                            Integer.parseInt(edge.getSrcPort()));
                            
                    controller.flowService.addFlow(buildFlow(flowMatch, flowAction, edge));
                }
            }
        }
    }
}
