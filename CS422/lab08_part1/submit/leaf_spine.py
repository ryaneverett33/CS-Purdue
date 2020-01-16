from mininet.net import Mininet
from mininet.topo import Topo
from mininet.cli import CLI
from mininet.node import RemoteController
from mininet.node import RemoteController, Host, OVSKernelSwitch

from mininet.link import TCLink
from argparse import ArgumentParser

# Function to parse the command line arguments
def parseOptions():

    # Create a parser object
    parser = ArgumentParser("Create a network with leaf and spine topology")

    # Add argument to the parser for nSpine, nLeaf and fanout options
    parser.add_argument('--spine', type=int, help='Number of Spine switches')
    parser.add_argument('--leaf', type=int, help='Number of Leaf switches')
    parser.add_argument('--fanout', type=int, help='Number of hosts per Lead switch')

    # Parse the command line arguments
    args = parser.parse_args()

    # Set the default values for arguments
    nSpine = 2
    nLeaf = 3
    fanout = 2

    # Change the values if passed on command line
    if args.spine:
        nSpine = args.spine

    if args.leaf:
        nLeaf = args.leaf

    if args.fanout:
        fanout = args.fanout

    # return the values
    return nSpine, nLeaf, fanout




class LeafAndSpine(Topo):
    spines = []
    leafs = []
    hostCount = 0
    def __init__(self, spine=2, leaf=2, fanout=2, **opts):
        "Create Leaf and Spine Topo."

        Topo.__init__(self, **opts)
        
     # This function builds a leaf and spine topology
     # Parameters passed to this function are
     #
     #    spine - Number of Spine switches
     #    leaf  - Number of Leaf switches
     #    fanout - Number of hosts per leaf switch
     #
        # spine401, spine402
        # leaf1, leaf2
        # h1, h2, h3 h1's MAC address is 00:00:00:00:00:01
        # leaf1 is linked to spine401 and spine402, leaf2 is linked to spine401 and spine402
        # h1 is linked to leaf1, h2 is linked to leaf2, etc
        for i in range(0, spine):
            spineName = self.addSwitch('spine40' + str((i + 1)))
            self.spines.append(spineName)
        for i in range(0, leaf):
            leafName = self.addSwitch('leaf' + str((i + 1)))
            self.leafs.append(leafName)
            for spine in self.spines:
                self.addLink(leafName, spine)
        for leaf in self.leafs:
            for i in range(0, fanout):
                # https://mailman.stanford.edu/pipermail/mininet-discuss/2015-February/005738.html
                host = self.addHost('h' + str((self.hostCount + 1)), mac=self.generateMac(self.hostCount + 1))
                self.addLink(leaf, host)
                self.hostCount = self.hostCount + 1

    def generateMac(self, number):
        # 00:00:00:00:00:01
        # [00-ff, 00-ff, 00-ff, 00-ff, 00-ff, 00-ff]
        # [0-255, 0-255, 0-255, 0-255, 0-255, 0-255]

        # hex(100*255*255) = '0x633864', hex(1) = '0x1'
        pairs = []
        value = hex(number)
        # '633864', '1'
        strippedValue = value[2:len(value)]
        i = 0
        # split into pairs
        while i < len(strippedValue):
            # get pairs of values
            a = strippedValue[i]
            if (i + 1) >= len(strippedValue):
                pairs.append('0' + a)
            else:
                b = strippedValue[i + 1]
                i = i + 1
                pairs.append(a + b)
            i = i + 1
        finalPairs = []  # ends with 6 final pairs
        emptyPairs = 6 - len(pairs)
        # generate empty pairs
        for i in range(0, emptyPairs):
            finalPairs.append('00')
        # copy original pairs
        for pair in pairs:
            finalPairs.append(pair)
        return '{0}:{1}:{2}:{3}:{4}:{5}'.format(
            finalPairs[0], finalPairs[1], finalPairs[2],
            finalPairs[3], finalPairs[4], finalPairs[5])

if __name__ == '__main__':
    
 
    nSpine, nLeaf, fanout = parseOptions()

    topo = LeafAndSpine(nSpine, nLeaf, fanout)
    net = Mininet(topo, autoSetMacs=True, xterms=False, controller=RemoteController, switch=OVSKernelSwitch)
    net.addController('c', ip='127.0.0.1', port=6633)  
   
    net.start()
    
    CLI(net)
    net.stop()
