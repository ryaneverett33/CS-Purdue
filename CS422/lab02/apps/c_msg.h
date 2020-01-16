#define C_REQUEST 1
#define C_RESPONSE 2
#define C_ERR  3
#define C_FILENAME_LEN 50
#define DEBUG 0

#pragma pack(1)
struct c_msg {
    
    int mtype;              //C_REQUEST or C_RESPONSE etc
    char filename[C_FILENAME_LEN];      //name of the file requested, assuming null terminated
    //int maxsize;
    //int actualsize;
    union{
	    int maxsize;
	    int actualsize;

    }; 


        
};
#pragma pack(0)