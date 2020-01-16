//From: https://gist.github.com/pasterp/27ccff8ddadcf7e90cc793c014c9264c
#include <errno.h>
#include <netinet/in.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <arpa/inet.h>

int main(int argc, char const *argv[])
{
	int sockfd, nbOctetsRecus;
	struct sockaddr_in serveurAddr, clientAddr;
	socklen_t len;

	char sendLine[1000];
	char recvLine[1000];

	if(argc != 2){
		printf("Usage %s <Adresse IP>\n", argv[0]);
		exit(EXIT_FAILURE);
	}

	//Création socket
	sockfd = socket(AF_INET, SOCK_DGRAM, 0);

    //Def adresse serveur
    memset(&serveurAddr, 0, sizeof(serveurAddr));
    serveurAddr.sin_family = AF_INET;
    serveurAddr.sin_addr.s_addr = inet_addr(argv[1]);
    serveurAddr.sin_port = htons(50008);

    //On lit une chaine
    while(fgets(sendLine, 1000, stdin) != NULL){

        //Envoi au serveur de la chaine
        sendto(sockfd, sendLine, strlen(sendLine), 0, (struct sockaddr *)&serveurAddr, sizeof(serveurAddr));

        //Reception du message du serveur
        nbOctetsRecus = recvfrom(sockfd, recvLine, 1000, 0, NULL, NULL);
        //Ajout char de fin de ligne
        recvLine[nbOctetsRecus]='\0';

        //Affichage du message
        printf("Serveur> %s", recvLine);


    }



	return 0;
}
