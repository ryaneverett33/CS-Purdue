/* packetdump.c - packetdump */

#include <xinu.h>

void	packetdump (
		struct	netpacket *pptr
		)
{
	//SOURCE -> DESTINATION, PACKET_TYPE, FIRST_15_BYTES_AFTER_ETHERNET_TYPE_IN_HEXADECIMAL\n
	//00:1a:a0:df:90:5d -> ff:ff:ff:ff:ff:ff, ARP, 00 01 08 00 06 04 00 02 00 1a a0 df 90 5d 80
	//98:4f:ee:00:1e:45 -> ff:ff:ff:ff:ff:ff, IPv4, 45 00 01 04 00 00 40 00 40 11 28 11 80 0a 88
	if (pptr == NULL)
		return;
	//print SOURCE
	for (int i = 0; i < ETH_ADDR_LEN; i++) {
		kprintf("%02x", pptr->net_ethsrc[i]);
		if (i != ETH_ADDR_LEN -1) {
			kprintf(":");
		}
	}
	kprintf(" -> ");
	//print DESTINATION
	for (int i = 0; i < ETH_ADDR_LEN; i++) {
		kprintf("%02x", pptr->net_ethdst[i]);
		if (i != ETH_ADDR_LEN -1) {
			kprintf(":");
		}
	}
	//PRINT PACKET TYPE
	switch (pptr->net_ethtype) {
		case ETH_ARP:
			kprintf(", ARP, ");
			break;
		case ETH_IP:
			kprintf(", IPv4, ");
			break;
		/*case ETH_IPv6:
			kprintf(", IPv6, ");
			break;*/
		default:
			kprintf(", 0x%04x, ", pptr->net_ethtype);
			break;
	}
	char * pointer = (char*)pptr;
	pointer += (int)(sizeof(byte) * ETH_ADDR_LEN);
	pointer += (int)(sizeof(byte) * ETH_ADDR_LEN);
	pointer += (int)sizeof(uint16);
	byte * bytearr = (byte*)pointer;
	for (int i = 0; i < 15; i++) {
		kprintf("%02x", bytearr[i]);
		if (i != 14)
			kprintf(" ");
	}
	kprintf("\n");
}

void packetdump_out(struct netpacket *pptr) {
	//DESTINATION <- SOURCE, PACKET_TYPE, FIRST_15_BYTES_AFTER_ETHERNET_TYPE_IN_HEXADECIMAL\n
	//aa:aa:aa:aa:aa:aa <- bb:bb:bb:bb:bb:bb, IPv4, 45 00 01 15 00 03 00 00 ff 11 b2 1e 80 0a 88\n
	if (pptr == NULL)
		return;
	//print DESTINATION
	for (int i = 0; i < ETH_ADDR_LEN; i++) {
		kprintf("%02x", pptr->net_ethdst[i]);
		if (i != ETH_ADDR_LEN -1) {
			kprintf(":");
		}
	}
	kprintf(" <- ");
	//print SOURCE
	for (int i = 0; i < ETH_ADDR_LEN; i++) {
		kprintf("%02x", pptr->net_ethsrc[i]);
		if (i != ETH_ADDR_LEN -1) {
			kprintf(":");
		}
	}
	//PRINT PACKET TYPE
	switch (ntohs(pptr->net_ethtype)) {
		case ETH_ARP:
			kprintf(", ARP, ");
			break;
		case ETH_IP:
			kprintf(", IPv4, ");
			break;
		/*case ETH_IPv6:
			kprintf(", IPv6, ");
			break;*/
		default:
			kprintf(", 0x%04x, ", pptr->net_ethtype);
			break;
	}
	char * pointer = (char*)pptr;
	pointer += (int)(sizeof(byte) * ETH_ADDR_LEN);
	pointer += (int)(sizeof(byte) * ETH_ADDR_LEN);
	pointer += (int)sizeof(uint16);
	byte * bytearr = (byte*)pointer;
	for (int i = 0; i < 15; i++) {
		kprintf("%02x", bytearr[i]);
		if (i != 14)
			kprintf(" ");
	}
	kprintf("\n");
}
