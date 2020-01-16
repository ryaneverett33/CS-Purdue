/* packetdump.c - packetdump */

#include <xinu.h>

void printIpAddress(uint32 address) {
	byte bytes[4];
	memset(&bytes, 0, sizeof(byte) * 4);
	//& 0xFF
	bytes[0] = address & 0xFF;
	bytes[1] = (address >> 8) & 0xFF;
	bytes[2] = (address >> 16) & 0xFF;
	bytes[3] = (address >> 24) & 0xFF;
	kprintf("%d.%d.%d.%d", bytes[0], bytes[1], bytes[2], bytes[3]);
}
byte getVersion(struct netpacket *pptr) {
	return (pptr->net_ipvh >> 4);
}
byte getIhl(struct netpacket *pptr) {
	return ((((pptr->net_ipvh << 4) << 24) >> 24) >> 4);
}
void printPayload(struct netpacket *pptr) {
	char * pointer = (char*)pptr;
	pointer += ((getIhl(pptr) - 1) * 8) + 2;
	byte *bytearr = (byte *)pointer;
	for (int i = 0; i < 15; i++) {
		kprintf("%02x", bytearr[i]);
		if (i != 14)
			kprintf(" ");
	}
}
void findStartPoint(struct netpacket *pptr) {
	int searchValue = 0;
	int searchValue2 = 0;
	switch (pptr->net_ipproto) {
		case TCP:
			searchValue = 0xa5;
			searchValue2 = 0xea;
			break;
		case ICMP:
			searchValue = 0x08;
			searchValue2 = 0x00;
			break;
		default:
			return;
	}
	int foundAt = -1;
	if (searchValue != 0) {
		//find where
		char *pointer = (char *)pptr;
		byte *bytearr = (byte *)pointer;
		for (int i = 0; i < pptr->net_iplen; i++) {
			if (bytearr[i] == searchValue) {
				if (i + 1 < pptr->net_iplen && bytearr[i + 1] == searchValue2) {
					foundAt = i;
					break;
				}
			}
		}
		if (foundAt == -1) {
			kprintf(" couldn't find ");
		}
		else {
			kprintf(" Found start at %d, ihl: %d ", foundAt, getIhl(pptr));
		}
	}
}
void printRawPacket(struct netpacket *pptr) {
	char *pointer = (char *)pptr;
	byte *bytearr = (byte *)pointer;
	for (int i = 0; i < pptr->net_iplen; i++) {
		kprintf("%02x  ", bytearr[i]);
	}
}
void printIp(struct netpacket *pptr) {
	//SOURCE_IP -> DESTINATION_IP, PROTOCOL_VERSION, 
	//IHL, TOTAL_PACKET_LENGTH, PROTOCOL_TYPE, FIRST_15_BYTES_OF_PAYLOAD

	//print SRC IP
	printIpAddress(pptr->net_ipsrc);
	kprintf(" -> ");
	//print DEST IP
	printIpAddress(pptr->net_ipdst);
	kprintf(", ");
	//print VERSION, IHL, TOTAL_PACKET_LENGTH
	kprintf("%d, %d, %d, ", getVersion(pptr), getIhl(pptr), ntohs(pptr->net_iplen));
	//print PROTOCOL TYPE
	//kprintf("Raw type: %d", pptr->net_ipproto);
	switch (pptr->net_ipproto) {
		case TCP:
			kprintf("TCP, ");
			break;
		case UDP:
			kprintf("UDP, ");
			break;
		case ICMP:
			kprintf("ICMP, ");
			break;
		default:
			kprintf("%02x, ", pptr->net_ipproto);
			break;
	}
	//findStartPoint(pptr);
	/*if (pptr->net_ipproto == ICMP || pptr->net_ipproto == TCP) {
		printRawPacket(pptr);
	}*/
	printPayload(pptr);
}
void printArp(struct netpacket *pptr) {
	//00 01 08 00 06 04 00 01 18 03 73 1d 33 07 80
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
}

void	packetdump (
		struct	netpacket *pptr
		)
{
	//ETH_SRC -> ETH_DST, ETH_TYPE
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
			printArp(pptr);
			break;
		case ETH_IP:
			kprintf(", IPv4, ");
			printIp(pptr);
			break;
		/*case ETH_IPv6:
			kprintf(", IPv6, ");
			break;*/
		default:
			kprintf(", 0x%04x, ", pptr->net_ethtype);
			printArp(pptr);
			break;
	}
	kprintf("\n");
}


