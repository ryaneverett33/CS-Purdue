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
void printMAC(byte * address, int len) {
	for (int i = 0; i < len; i++) {
		kprintf("%02x", address[i]);
		if (i != ETH_ADDR_LEN - 1) {
			kprintf(":");
		}
	}
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
void printIpv6(struct netpacket *pptr) {
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
	kprintf(", 0x%04x, ", pptr->net_ethtype);
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

//lab06 print IPv4
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
	kprintf("%02x, ", pptr->net_ipproto);
	printPayload(pptr);
	kprintf("\n");
}

/*void printArp(struct netpacket *pptr) {
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
}*/

//ETH_SRC -> ETH_DST,
void printSrcDst(struct netpacket *pkt) {
	/*for (int i = 0; i < ETH_ADDR_LEN; i++) {
		kprintf("%02x", pkt->net_ethsrc[i]);
		if (i != ETH_ADDR_LEN - 1) {
			kprintf(":");
		}
	}*/
	printMAC((byte*)&pkt->net_ethsrc, ETH_ADDR_LEN);
	kprintf(" -> ");
	//print DESTINATION
	/*for (int i = 0; i < ETH_ADDR_LEN; i++) {
		kprintf("%02x", pkt->net_ethdst[i]);
		if (i != ETH_ADDR_LEN - 1) {
			kprintf(":");
		}
	}*/
	printMAC((byte*)&pkt->net_ethdst, ETH_ADDR_LEN);
	kprintf(", ");
}
//SOURCE_IP -> DESTINATION_IP,
void printSrcDstIp(struct netpacket *pkt) {
	//print SRC IP
	printIpAddress(pkt->net_ipsrc);
	kprintf(" -> ");
	//print DEST IP
	printIpAddress(pkt->net_ipdst);
	kprintf(", ");
}

void packetdump_arp(struct netpacket *pkt) {
	struct arppacket * arppkt = (struct arppacket*)pkt;
	//If Request
	//ETH_SRC -> ETH_DST, ETH_TYPE, REQUEST, HLEN, PLEN, SOURCE_IP[SOURCE_ETH_ADDR] -> TARGET_IP

	//If Reply
	//ETH_SRC -> ETH_DST, ETH_TYPE, REPLY, HLEN, PLEN, SOURCE_IP[SOURCE_ETH_ADDR] -> TARGET_IP[TARGET_ETH_ADDR]

	//aa:aa:aa:aa:aa:aa -> bb:bb:bb:bb:bb:bb, ARP, REQUEST, 6, 4, 128.10.3.250[aa:aa:aa:aa:aa:aa] -> 128.10.3.253
	//aa:aa:aa:aa:aa:aa -> bb:bb:bb:bb:bb:bb, ARP, REPLY, 6, 4, 128.10.3.2[aa:aa:aa:aa:aa:aa] -> 128.10.3.51[cc:cc:cc:cc:cc:cc]
	printSrcDst(pkt);
	kprintf("ARP, ");
	//printf REQUEST or REPLY
	switch (arppkt->arp_op) {
		case ARP_REQUEST:
			kprintf("REQUEST, ");
			break;
		case ARP_REPLY:
			kprintf("REPLY, ");
			break;
		default:
			kprintf("OP: %d, ", arppkt->arp_op);
	}
	kprintf("%d, %d, ", arppkt->arp_hlen, arppkt->arp_plen);
	printIpAddress(arppkt->arp_sndpa);
	kprintf("[");
	printMAC((byte*)&arppkt->arp_sndha, ARP_HALEN);
	kprintf("] -> ");
	printIpAddress(arppkt->arp_tarpa);
	if (arppkt->arp_op == ARP_REPLY) {
		kprintf("[");
		printMAC((byte*)&arppkt->arp_tarha, ARP_HALEN);
		kprintf("]");
	}
	kprintf("\n");
}

void packetdump_icmp(struct netpacket *pkt) {
	//If Echo-Request
	//ETH_SRC -> ETH_DST, ETH_TYPE, SOURCE_IP -> DESTINATION_IP, PROTOCOL_VERSION, IHL, 
	//TOTAL_PACKET_LENGTH, PROTOCOL_TYPE, ECHO_REQUEST, id = identifier, seq = sequence

	//If Echo-Reply
	//ETH_SRC -> ETH_DST, ETH_TYPE, SOURCE_IP -> DESTINATION_IP, PROTOCOL_VERSION, IHL,
	//TOTAL_PACKET_LENGTH, PROTOCOL_TYPE, ECHO_REPLY, id = identifier, seq = sequence

	//Else
	//ETH_SRC -> ETH_DST, ETH_TYPE, SOURCE_IP -> DESTINATION_IP, PROTOCOL_VERSION, IHL,
	//TOTAL_PACKET_LENGTH, PROTOCOL_TYPE, ICMP_TYPE_IN_HEX

	//aa:aa:aa:aa:aa:aa -> bb:bb:bb:bb:bb:bb, IPv4, 128.10.3.31 -> 128.10.3.102, 4, 5, 84, ICMP, ECHO_REPLY, id = 10996, seq = 1
	//aa:aa:aa:aa:aa:aa -> bb:bb:bb:bb:bb:bb, IPv4, 128.10.3.31 -> 128.10.3.102, 4, 5, 84, ICMP, 0x03
	printSrcDst(pkt);
	kprintf("IPv4, ");
	printSrcDstIp(pkt);
	kprintf("%d, %d, %d, ICMP, ", getVersion(pkt), getIhl(pkt), ntohs(pkt->net_iplen));
	//print ICMP type
	switch(pkt->net_ictype) {
		case ICMP_ECHO_REPLY:
			kprintf("ECHO_REPLY, ");
			break;
		case ICMP_ECHO_REQUEST:
			kprintf("ECHO_REQUEST, ");
			break;
		default:
			kprintf("0x%02x, ", pkt->net_ictype);
			break;
	}
	kprintf("id = %d, seq = %d\n", ntohs(pkt->net_icident), ntohs(pkt->net_icseq));
}

void packetdump_udp(struct netpacket *pkt) {
	//ETH_SRC -> ETH_DST, ETH_TYPE, SRC_IP -> DST_IP, PROTOCOL_VERSION, IHL, 
	//TOTAL_PACKET_LENGTH, PROTOCOL_TYPE, SRC_PORT, DST_PORT, CHECKSUM, UDP_LENGTH
	//aa:aa:aa:aa:aa:aa -> bb:bb:bb:bb:bb:bb, IPv4, 128.10.3.31 -> 128.10.3.102, 4, 5, 328, UDP, 41259, 2073 , 0xce0b, 308
	printSrcDst(pkt);
	kprintf("IPv4, ");
	printSrcDstIp(pkt);
	kprintf("%d, %d, %d, UDP, ", getVersion(pkt), getIhl(pkt), ntohs(pkt->net_iplen));
	kprintf("%d, %d, 0x%04x, %d\n", ntohs(pkt->net_udpsport), ntohs(pkt->net_udpdport), ntohs(pkt->net_udpcksum), ntohs(pkt->net_udplen));
}

void packetdump(struct netpacket *pptr) {
	//ETH_SRC -> ETH_DST, ETH_TYPE
	if (pptr == NULL)
		return;
	//print SOURCE
	/*for (int i = 0; i < ETH_ADDR_LEN; i++) {
		kprintf("%02x", pptr->net_ethsrc[i]);
		if (i != ETH_ADDR_LEN - 1) {
			kprintf(":");
		}
	}
	kprintf(" -> ");
	//print DESTINATION
	for (int i = 0; i < ETH_ADDR_LEN; i++) {
		kprintf("%02x", pptr->net_ethdst[i]);
		if (i != ETH_ADDR_LEN - 1) {
			kprintf(":");
		}
	}
	//PRINT PACKET TYPE
	switch (pptr->net_ethtype)
	{
	case ETH_ARP:
		kprintf(", ARP, ");
		printArp(pptr);
		break;
	case ETH_IP:
		kprintf(", IPv4, ");
		printIp(pptr);
		break;
	case ETH_IPv6:
			kprintf(", IPv6, ");
			break;
	default:
		kprintf(", 0x%04x, ", pptr->net_ethtype);
		printArp(pptr);
		break;
	}
	kprintf("\n");*/
	switch(pptr->net_ethtype) {
		case ETH_ARP:
			packetdump_arp(pptr);
			break;
		case ETH_IP:
			switch(pptr->net_ipproto) {
				case UDP:
					packetdump_udp(pptr);
					break;
				case ICMP:
					packetdump_icmp(pptr);
					break;
				default:
					// print like lab06
					printIp(pptr);
					break;
			}
			break;
		default:
			//print like lab05
			printIpv6(pptr);
			break;
	}
}
