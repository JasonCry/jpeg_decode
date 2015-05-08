

#include"../INC/jpeg.h"
#include"../INC/bmp.h"
#include "memory.h"
#include "math.h"
#include "stdio.h"
#include "malloc.h"

//macro definition
#define WIDTHBYTES(i)    ((i+31)/32*4)//ĩβ�ֽ�����Ϊ8��ʱ��0����
#define PI 3.1415926535
//define return value of function
#define FUNC_OK 0
#define FUNC_MEMORY_ERROR 1
#define FUNC_FILE_ERROR 2
#define FUNC_FORMAT_ERROR 3
#define pi 3.14159

//////////////////////////////////////////////////
//Jpeg functions
BOOL LoadJpegFile(char *JpegFileName);
void showerror(int funcret);
int  InitTag();
void InitTable();
int  Decode();
int  DecodeMCUBlock();
int  HufBlock(BYTE dchufindex,BYTE achufindex);
int  DecodeElement();
void IQtIZzMCUComponent(short flag);
void IQtIZzBlock(short  *s ,int * d,short flag);
void GetYUV(short flag);
void StoreBuffer();
BYTE ReadByte();
//void Initialize_Fast_IDCT();
//void Fast_IDCT(int * block);
//void idctrow(int * blk);
//void idctcol(int * blk);
//void Fast_IDCT1(int *block);

void Fast_IDCT3(int *in_put, int *out_put);
//////////////////////////////////////////////////
//global variable declaration
BITMAPFILEHEADER   bf;
BITMAPINFOHEADER   bi;
char *hImgData=NULL;
DWORD              NumColors;
DWORD              LineBytes;
DWORD              ImgWidth=0 , ImgHeight=0;
char*             lpPtr;
//////////////////////////////////////////////////
//variables used in jpeg function
short   SampRate_Y_H,SampRate_Y_V;
short   SampRate_U_H,SampRate_U_V;//Y��U��V�Ĳ���ϵ��
short   SampRate_V_H,SampRate_V_V;
short   H_YtoU,V_YtoU,H_YtoV,V_YtoV;
short   Y_in_MCU,U_in_MCU,V_in_MCU;
unsigned char   *lp;
short   qt_table[3][64];
short   comp_num;
BYTE   comp_index[3];
BYTE      YDcIndex,YAcIndex,UVDcIndex,UVAcIndex;
BYTE   HufTabIndex;
short      *YQtTable,*UQtTable,*VQtTable;
BYTE   And[9]={0,1,3,7,0xf,0x1f,0x3f,0x7f,0xff};
short      code_pos_table[4][16],code_len_table[4][16];
unsigned short code_value_table[4][256];
unsigned short huf_max_value[4][16],huf_min_value[4][16];
short   BitPos,CurByte;
short   rrun,vvalue;
short   MCUBuffer[10*64];
int    QtZzMCUBuffer[10*64];
short   BlockBuffer[64];
short   ycoef,ucoef,vcoef;
int    Y[4*64],U[4*64],V[4*64];
DWORD      sizei,sizej;
static  long iclp[1024];

void showerror(int funcret)
{
	switch(funcret)
	{
	case FUNC_MEMORY_ERROR:
		printf("Error alloc memory/n!");
		break;
	case FUNC_FILE_ERROR:
		printf("File not found!/n");
		break;
	case FUNC_FORMAT_ERROR:
		printf("File format error!/n");
		break;
	}
}

int InitTag(char *lpJpegBuf)
{
	BOOL finish=FALSE;
	BYTE id;
	short  llength;
	short  i,j,k;
	short  huftab1,huftab2;
	short  huftabindex;
	BYTE hf_table_index;
	BYTE qt_table_index;
	BYTE comnum;

	unsigned char  *lptemp;
	short  ccount;
	
	lp=lpJpegBuf+2;//ָ���ռ�ĵڶ�����ַ

	while (!finish){
		id=*(lp+1);
		lp+=2;
		switch (id){
		case M_APP0://ͼ��ʶ����Ϣffeo
			llength=MAKEWORD(*(lp+1),*lp);//���γ���
			lp+=llength;
		
			break;
		case M_DQT://������ffdb
			llength=MAKEWORD(*(lp+1),*lp);
			qt_table_index=(*(lp+2))&0x0f;//ȡ����λΪqt��
			lptemp=lp+3;
			if(llength<80){
				for(i=0;i<64;i++)
					qt_table[qt_table_index][i]=(short)*(lptemp++);
			}
			else{//����������������һ�����е����
				for(i=0;i<64;i++)
					qt_table[qt_table_index][i]=(short)*(lptemp++);    
	          //for(i=0;i<64;i++)
				//printf("%d   ",qt_table[qt_table_index][i]);printf("\n");
			//printf("\n*************\n");
			qt_table_index=(*(lptemp++))&0x0f;
				for(i=0;i<64;i++)
					qt_table[qt_table_index][i]=(short)*(lptemp++);
             //for(i=0;i<64;i++)
			//	printf("%d   ",qt_table[qt_table_index][i]);printf("\n");
			//printf("\n*************\n");
			}
			lp+=llength;  
			//for(i=0;i<64;i++)
			//	printf("%d   ",qt_table[qt_table_index][i]);printf("\n");
		//	printf("\n*************\n");
			break;
		case M_SOF0://ͼ����Ϣ��
			llength=MAKEWORD(*(lp+1),*lp);
			ImgHeight=MAKEWORD(*(lp+4),*(lp+3));//ͼƬ�߶�
			ImgWidth=MAKEWORD(*(lp+6),*(lp+5));//ͼƬ���
            comp_num=*(lp+7);//�������
			if((comp_num!=1)&&(comp_num!=3))
				return FUNC_FORMAT_ERROR;
			if(comp_num==3){
				comp_index[0]=*(lp+8);
				SampRate_Y_H=(*(lp+9))>>4;//ˮƽ����ϵ��
				SampRate_Y_V=(*(lp+9))&0x0f;//��ֱ����ϵ��
				YQtTable=(short *)qt_table[*(lp+10)];//Yʹ�õ�������
				//printf("%d\n",YQtTable);
				comp_index[1]=*(lp+11);
				SampRate_U_H=(*(lp+12))>>4;
				SampRate_U_V=(*(lp+12))&0x0f;
				UQtTable=(short *)qt_table[*(lp+13)];
				//printf("%d\n",UQtTable);
				comp_index[2]=*(lp+14);
				SampRate_V_H=(*(lp+15))>>4;
				SampRate_V_V=(*(lp+15))&0x0f;
				VQtTable=(short *)qt_table[*(lp+16)];
				//printf("%d\n",VQtTable);
			}
			else{//�����Ϊ1ʱ
				comp_index[0]=*(lp+8);
				SampRate_Y_H=(*(lp+9))>>4;
				SampRate_Y_V=(*(lp+9))&0x0f;
				YQtTable=(short *)qt_table[*(lp+10)];
				
				comp_index[1]=*(lp+8);
				SampRate_U_H=1;
				SampRate_U_V=1;
				UQtTable=(short *)qt_table[*(lp+10)];
				
				comp_index[2]=*(lp+8);
				SampRate_V_H=1;
				SampRate_V_V=1;
				VQtTable=(short *)qt_table[*(lp+10)];
			}
			lp+=llength;          
			break;
		case M_DHT:  //huffman��ffc4           
			llength=MAKEWORD(*(lp+1),*lp);
			if (llength<0xd0){
				huftab1=(short)(*(lp+2))>>4;     //huftab1=0,1
				huftab2=(short)(*(lp+2))&0x0f;   //huftab2=0,1
				huftabindex=huftab1*2+huftab2;
				lptemp=lp+3;
				for (i=0; i<16; i++)
					code_len_table[huftabindex][i]=(short)(*(lptemp++));
				j=0;
				for (i=0; i<16; i++)
					if(code_len_table[huftabindex][i]!=0){
						k=0;
						while(k<code_len_table[huftabindex][i]){
							code_value_table[huftabindex][k+j]=(short)(*(lptemp++));
							k++;
						}
						j+=k; 
					}
					i=0;
					while (code_len_table[huftabindex][i]==0)
						i++;
					for (j=0;j<i;j++){
						huf_min_value[huftabindex][j]=0;
						huf_max_value[huftabindex][j]=0;
					}
					huf_min_value[huftabindex][i]=0;
					huf_max_value[huftabindex][i]=code_len_table[huftabindex][i]-1;
					for (j=i+1;j<16;j++){
						huf_min_value[huftabindex][j]=(huf_max_value[huftabindex][j-1]+1)<<1;
						huf_max_value[huftabindex][j]=huf_min_value[huftabindex][j]+code_len_table[huftabindex][j]-1;
					}
					code_pos_table[huftabindex][0]=0;
					for (j=1;j<16;j++)
						code_pos_table[huftabindex][j]=code_len_table[huftabindex][j-1]+code_pos_table[huftabindex][j-1];
					lp+=llength;

					for (j=0;j<code_pos_table[huftabindex][15]+code_len_table[huftabindex][15];j++)
					{
						printf("%d    ",code_value_table[huftabindex][j]);
						//printf("%x    ",huf_min_value[huftabindex][j]);
						//printf("\n");
					}
					printf("\n************\n");
		}  //���ɸ�����������С�����������
			else{//�ĸ�huffman����һ������
				hf_table_index=*(lp+2);
				lp+=2;
				while (hf_table_index!=0xff){
					huftab1=(short)hf_table_index>>4;     //huftab1=0,1
					huftab2=(short)hf_table_index&0x0f;   //huftab2=0,1
					huftabindex=huftab1*2+huftab2;
					lptemp=lp+1;
					ccount=0;
					for (i=0; i<16; i++){
						code_len_table[huftabindex][i]=(short)(*(lptemp++));
						ccount+=code_len_table[huftabindex][i];
					}
					ccount+=17; 
					j=0;
					for (i=0; i<16; i++)
						if(code_len_table[huftabindex][i]!=0){
							k=0;
							while(k<code_len_table[huftabindex][i])
							{
								code_value_table[huftabindex][k+j]=(short)(*(lptemp++));
								k++;
							}
							j+=k;
						}
						i=0;
						while (code_len_table[huftabindex][i]==0)
							i++;
						for (j=0;j<i;j++){
							huf_min_value[huftabindex][j]=0;
							huf_max_value[huftabindex][j]=0;
						}
						huf_min_value[huftabindex][i]=0;
						huf_max_value[huftabindex][i]=code_len_table[huftabindex][i]-1;
						for (j=i+1;j<16;j++){
							huf_min_value[huftabindex][j]=(huf_max_value[huftabindex][j-1]+1)<<1;
							huf_max_value[huftabindex][j]=huf_min_value[huftabindex][j]+code_len_table[huftabindex][j]-1;
						}
						code_pos_table[huftabindex][0]=0;
						for (j=1;j<16;j++)
							code_pos_table[huftabindex][j]=code_len_table[huftabindex][j-1]+code_pos_table[huftabindex][j-1];
						lp+=ccount;
						hf_table_index=*lp;
						//for (j=0;j<code_pos_table[huftabindex][15]+code_len_table[huftabindex][15];j++)
				//	{
					//	printf("%d    ",code_value_table[huftabindex][j]);
						//printf("%x    ",huf_min_value[huftabindex][j]);
						//printf("\n");
					//}
				//	printf("\n************\n");

				}  //while
			}  //else
			break;

		case M_SOS://ͼ�����ݶ�
			llength=MAKEWORD(*(lp+1),*lp);
			comnum=*(lp+2);
			if(comnum!=comp_num)
				return FUNC_FORMAT_ERROR;
			lptemp=lp+3;
			for (i=0;i<comp_num;i++){
				if(*lptemp==comp_index[0]){
					YDcIndex=(*(lptemp+1))>>4;   //Y
					YAcIndex=((*(lptemp+1))&0x0f)+2;
				}
				else{
					UVDcIndex=(*(lptemp+1))>>4;   //U,V
					UVAcIndex=((*(lptemp+1))&0x0f)+2;
				}
				lptemp+=2;
			}
			lp+=llength;
			finish=TRUE;
			break;
		case M_EOI://������    
			return FUNC_FORMAT_ERROR;
			break;
		default://������ε�������
			if ((id&0xf0)!=0xd0){
				llength=MAKEWORD(*(lp+1),*lp);
				lp+=llength;
			}
			else lp+=2;
			break;
    }  
 } 

 return FUNC_OK;
}
void InitTable()
{
	short i,j;
	sizei=sizej=0;
	ImgWidth=ImgHeight=0;
	rrun=vvalue=0;
	BitPos=0;
	CurByte=0;

	for(i=0;i<3;i++)
		for(j=0;j<64;j++)
			qt_table[i][j]=0;//��ʼ��������
		comp_num=0;
		HufTabIndex=0;
		for(i=0;i<3;i++)
			comp_index[i]=0;
		for(i=0;i<4;i++)
			for(j=0;j<16;j++){
				code_len_table[i][j]=0;
				code_pos_table[i][j]=0;
				huf_max_value[i][j]=0;
				huf_min_value[i][j]=0;
			}
			for(i=0;i<4;i++)
				for(j=0;j<256;j++)
					code_value_table[i][j]=0;
				
				for(i=0;i<10*64;i++){
					MCUBuffer[i]=0;
					QtZzMCUBuffer[i]=0;
				}
				for(i=0;i<64;i++){
					Y[i]=0;
					U[i]=0;
					V[i]=0;
					BlockBuffer[i]=0;
				}
				ycoef=ucoef=vcoef=0;
}
/////////////////////////////////////////////////////////////////////////
int Decode( BYTE *lpPtr)
{
	int funcret;
	
	Y_in_MCU=SampRate_Y_H*SampRate_Y_V;
	U_in_MCU=SampRate_U_H*SampRate_U_V;
	V_in_MCU=SampRate_V_H*SampRate_V_V;
	H_YtoU=SampRate_Y_H/SampRate_U_H;
	V_YtoU=SampRate_Y_V/SampRate_U_V;
	H_YtoV=SampRate_Y_H/SampRate_V_H;
	V_YtoV=SampRate_Y_V/SampRate_V_V;
	//Initialize_Fast_IDCT();
	while((funcret=DecodeMCUBlock())==FUNC_OK)//������С���뵥Ԫ
	{
		IQtIZzMCUComponent(0);//��Z��������������ɢ����
		IQtIZzMCUComponent(1);
		IQtIZzMCUComponent(2);
		GetYUV(0);//���YUV��ֵ
		GetYUV(1);
		GetYUV(2);
		StoreBuffer();
		sizej+=SampRate_Y_H*8;
		if(sizej>=ImgWidth){
			sizej=0;
			sizei+=SampRate_Y_V*8;
		}
		if ((sizej==0)&&(sizei>=ImgHeight))//�ж��Ƿ��ȡ��β
			break;
	}
	return funcret;
}
/////////////////////////////////////////////////////////////////////////////////////////
void  GetYUV(short flag)
{
	short H,VV;
	short i,j,k,h;
	int  *buf;
	int  *pQtZzMCU;
	
	switch(flag){
	case 0:
		H=SampRate_Y_H;
		VV=SampRate_Y_V;
		buf=Y;
		pQtZzMCU=QtZzMCUBuffer;//�洢���롢��Z ������������ɢ���ұ任��ֵ
		break;
	case 1:
		H=SampRate_U_H;
		VV=SampRate_U_V;
		buf=U;
		pQtZzMCU=QtZzMCUBuffer+Y_in_MCU*64;
		break;
	case 2:
		H=SampRate_V_H;
		VV=SampRate_V_V;
		buf=V;
		pQtZzMCU=QtZzMCUBuffer+(Y_in_MCU+U_in_MCU)*64;
		break;
	}
	for (i=0;i<VV;i++)
		for(j=0;j<H;j++)
			for(k=0;k<8;k++)
				for(h=0;h<8;h++)
					buf[(i*8+k)*SampRate_Y_H*8+j*8+h]=*pQtZzMCU++;//����ֵ�洢��yuv��
} 
///////////////////////////////////////////////////////////////////////////////
void StoreBuffer()
{
	short i,j;
	unsigned char  *lpbmp;
	unsigned char R,G,B;
	int y,u,v,rr,gg,bb;
	
	for(i=0;i<SampRate_Y_V*8;i++){
		if((sizei+i)<ImgHeight){
			lpbmp=((unsigned char *)lpPtr+(DWORD)(ImgHeight-sizei-i-1)*LineBytes+sizej*3);//���ݲ��ֵĿ�ʼ��ַ
			for(j=0;j<SampRate_Y_H*8;j++){
				if((sizej+j)<ImgWidth){
					y=Y[i*8*SampRate_Y_H+j];
					u=U[(i/V_YtoU)*8*SampRate_Y_H+j/H_YtoU];
					v=V[(i/V_YtoV)*8*SampRate_Y_H+j/H_YtoV];
					rr=((y<<8)+18*u+367*v)>>8;
					gg=((y<<8)-159*u-220*v)>>8;
					bb=((y<<8)+411*u-29*v)>>8;
					R=(unsigned char)rr;
					G=(unsigned char)gg;
					B=(unsigned char)bb;
				 
				if (rr>255) R=255; else if (rr<0) R=0;
				 if (gg>255) G=255; else if (gg<0) G=0;
				 if (bb>255) B=255; else if (bb<0) B=0;
					*lpbmp++=B;
					*lpbmp++=G;
					*lpbmp++=R;
				}
				else  break;
			}
		}
		else break;
	}
}

///////////////////////////////////////////////////////////////////////////////
int DecodeMCUBlock()
{
	short *lpMCUBuffer;
	short i,j;
	int funcret;

	switch(comp_num){//ѡ�����
	case 3://��ɫͼ��
		lpMCUBuffer=MCUBuffer;//�洢�������ֵ
		for (i=0;i<SampRate_Y_H*SampRate_Y_V;i++)  //���ݲ���ֵ��ȡY��ֵ
		{
			funcret=HufBlock(YDcIndex,YAcIndex);
			if (funcret!=FUNC_OK)
				return funcret;
			BlockBuffer[0]=BlockBuffer[0]+ycoef;//����ǰһ��ydc��Ϊ���ڵ�ydc
			ycoef=BlockBuffer[0];
			for (j=0;j<64;j++)
				*lpMCUBuffer++=BlockBuffer[j];//��������ֵ������lpMCUBuffer��
		}
		for (i=0;i<SampRate_U_H*SampRate_U_V;i++)  //���ݲ���ֵ��ȡU��ֵ
		{
			funcret=HufBlock(UVDcIndex,UVAcIndex);
			if (funcret!=FUNC_OK)
				return funcret;
			BlockBuffer[0]=BlockBuffer[0]+ucoef;//����������������
			ucoef=BlockBuffer[0];
			for (j=0;j<64;j++)
				*lpMCUBuffer++=BlockBuffer[j];
		}
		for (i=0;i<SampRate_V_H*SampRate_V_V;i++)  //���ݲ���ֵ��ȡV��ֵ
		{
			funcret=HufBlock(UVDcIndex,UVAcIndex);
			if (funcret!=FUNC_OK)
				return funcret;
			BlockBuffer[0]=BlockBuffer[0]+vcoef;
			vcoef=BlockBuffer[0];
			for (j=0;j<64;j++)
				*lpMCUBuffer++=BlockBuffer[j];
		}
		break;
	case 1://�Ҷ�ͼ��
		lpMCUBuffer=MCUBuffer;
		funcret=HufBlock(YDcIndex,YAcIndex);

		if (funcret!=FUNC_OK)
			return funcret;

		BlockBuffer[0]=BlockBuffer[0]+ycoef;
		ycoef=BlockBuffer[0];

		for (j=0;j<64;j++)
			*lpMCUBuffer++=BlockBuffer[j];

		for (i=0;i<128;i++)
    		*lpMCUBuffer++=0;

		break;
	default:
		return FUNC_FORMAT_ERROR;
	}
	return FUNC_OK;
}
//////////////////////////////////////////////////////////////////
int HufBlock( BYTE dchufindex,BYTE achufindex)//�����mcu
{
	short count=0;
	short i;
	int funcret;
	
	//dc
	HufTabIndex=dchufindex;
	funcret=DecodeElement();//������ֽ�
	if(funcret!=FUNC_OK)
		return funcret;
	
	BlockBuffer[count++]=vvalue;
	//ac
	HufTabIndex=achufindex;
	while (count<64)
	{
		funcret=DecodeElement();
		if(funcret!=FUNC_OK)
			return funcret;
		if ((rrun==0)&&(vvalue==0)){//��ĸ���Ϊ0������ֵΪ0
			for (i=count;i<64;i++)
				BlockBuffer[i]=0;
			count=64;
		}
		else{
			for (i=0;i<rrun;i++)
				BlockBuffer[count++]=0;
			BlockBuffer[count++]=vvalue;//�洢��������ֵ
		}
	}
	return FUNC_OK;
}
/////////////////////////////////////////////////////////////////////////////
int DecodeElement()
{
	int thiscode,tempcode;
	unsigned short temp,valueex;
	short codelen;
	BYTE hufexbyte,runsize,tempsize,sign;
	BYTE newbyte,lastbyte;		
	if(BitPos>=1)//�ж�λ�ĸ����Ƿ����1
	{
		BitPos--;
		thiscode=(BYTE)CurByte>>BitPos;//��ȡ���λ
		CurByte=CurByte&And[BitPos];//��ȡ��λ
	}
	else
	{
		lastbyte=ReadByte();//��ȡ�ֽ�
		BitPos--;
		newbyte=CurByte&And[BitPos];//��ȥ���λ
		thiscode=lastbyte>>7;//���λ
		CurByte=newbyte;
	}

	codelen=1;

	while ((thiscode<huf_min_value[HufTabIndex][codelen-1])||(code_len_table[HufTabIndex][codelen-1]==0)||
		(thiscode>huf_max_value[HufTabIndex][codelen-1]))//��ֵ���������Χ�������ִ��
	{
		if(BitPos>=1)
		{
			BitPos--;
			tempcode=(BYTE)CurByte>>BitPos;//��ȡ���λ
			CurByte=CurByte&And[BitPos];
		}
		else//��ʼ��ȡ�ֽ�
		{
			lastbyte=ReadByte();
			BitPos--;
			newbyte=CurByte&And[BitPos];
			tempcode=(BYTE)lastbyte>>7;
			CurByte=newbyte;
		}
		thiscode=(thiscode<<1)+tempcode;
		codelen++;
		if(codelen>16)
			return FUNC_FORMAT_ERROR;
	}  //while
	temp=thiscode-huf_min_value[HufTabIndex][codelen-1]+code_pos_table[HufTabIndex][codelen-1];//�������Ӧ��ֵ��λ���±�
	hufexbyte=(BYTE)code_value_table[HufTabIndex][temp];//��Ŷ�Ӧ��huffmanֵ
	rrun=(short)(hufexbyte>>4);//����λΪ0�ĸ�����
	runsize=hufexbyte&0x0f;//����λΪ�����ƶ���λ��
	if(runsize==0)
	{
		vvalue=0;
		return FUNC_OK;
	}
	tempsize=runsize;//�����ƶ��ĸ���
	if(BitPos>=runsize)//ʣ�µ�λ��������
	{
        BitPos-=runsize;
		valueex=(BYTE)CurByte>>BitPos;//��������λ
		CurByte=CurByte&And[BitPos];//�õ�ʣ�µ�λ
	}
	else{//ʣ�µ�λ����������
		valueex=CurByte;
		tempsize-=BitPos;//�������Ҫ�ƶ���λ
		while(tempsize>8){//����һ���ֽ���һ����һ���ֵĶ�
			lastbyte=ReadByte();
			valueex=(valueex<<8)+(BYTE)lastbyte;
			tempsize-=8;
		}  
		lastbyte=ReadByte();
		BitPos-=tempsize;
		valueex=(valueex<<tempsize)+(lastbyte>>BitPos);
		CurByte=lastbyte&And[BitPos];
	}  
	sign=valueex>>(runsize-1);
	if(sign)
		vvalue=valueex;
	else{
		valueex=valueex^0xffff;//������
		temp=0xffff<<runsize;
		vvalue=-(short)(valueex^temp);//ÿ��λ��ȡ��
	}
	return FUNC_OK;
}
/////////////////////////////////////////////////////////////////////////////////////
void IQtIZzMCUComponent(short flag)
{
	short H,VV;
	short i,j;
	int *pQtZzMCUBuffer;
	short  *pMCUBuffer;
	
	switch(flag){
	case 0:
		H=SampRate_Y_H;
		VV=SampRate_Y_V;
		pMCUBuffer=MCUBuffer;//�洢���������
		pQtZzMCUBuffer=QtZzMCUBuffer;//�洢��Z��������������ɢ���Һ��ֵ
		break;
	case 1:
		H=SampRate_U_H;
		VV=SampRate_U_V;
		pMCUBuffer=MCUBuffer+Y_in_MCU*64;//���ÿռ��׵�ַ��
		pQtZzMCUBuffer=QtZzMCUBuffer+Y_in_MCU*64;
		break;
	case 2:
		H=SampRate_V_H;
		VV=SampRate_V_V;
		pMCUBuffer=MCUBuffer+(Y_in_MCU+U_in_MCU)*64;
		pQtZzMCUBuffer=QtZzMCUBuffer+(Y_in_MCU+U_in_MCU)*64;
		break;
	}
	for(i=0;i<VV;i++)
		for (j=0;j<H;j++)
			IQtIZzBlock(pMCUBuffer+(i*H+j)*64,pQtZzMCUBuffer+(i*H+j)*64,flag);//���ĸ�Y�ֱ�����������ɢ���Һ��ֵ
}

//////////////////////////////////////////////////////////////////////////////////////////
void IQtIZzBlock(short  *s ,int * d,short flag)//s�洢Դ���ݣ�dΪ�洢��Z��������������ɢ���Һ��ֵ
{
    short i,j;
    short tag;
    short *pQt;
    int buffer2[8][8];
    int *buffer1;
    short offset;
    int buffer3[64];

    switch(flag)
    {
        case 0:
            pQt=YQtTable;//��Ӧ������
            offset=128;//ƫ��������ѹ����Ϊ��ʹ��ֵ������������ĸ��������Լ�ȥ128�������ڽ�������ɢ���ұ任����Ҫ����128
            break;
        case 1:
            pQt=UQtTable;
            offset=0;
            break;
        case 2:
            pQt=VQtTable;
            offset=0;
            break;
    }

    for(i=0;i<8;i++)
        for(j=0;j<8;j++)
        {
            tag=Zig_Zag[i][j];
            buffer2[i][j]=(int)s[tag]*(int)pQt[tag];//��zig-zag���ֽ��з�����
        }
        buffer1=(int *)buffer2;//ȡ�׵�ַ
        //Fast_IDCT(buffer1);//��������ɢ����
        Fast_IDCT3(buffer1,buffer3);
    for(i=0;i<8;i++)
            for(j=0;j<8;j++)
                buffer2[i][j]=buffer3[i*8+j];
        for(i=0;i<8;i++)
            for(j=0;j<8;j++)
                d[i*8+j]=buffer2[i][j]+offset;//���ٸ���Ҷ�任��Ľ��
}

///////////////////////////////////////////////////////////////////////////////
/*void Fast_IDCT(int * block)
{
	short i;
	
	for (i=0; i<8; i++)
		idctrow(block+8*i);//���б任
	
	for (i=0; i<8; i++)
		idctcol(block+i);//���б任
}
*/
///////////////////////////////////////////////////////////////////////////////
int change(double c)
{
    if(c>0)
        return (int)(c+0.5);
    else
        return (int)(c-0.5);
}

void Fidct3row(int *ptest,int *output)
{
    int j;
    double B0,B1,B2,B3,B4,B5,B6,B7;
    double temp0,temp1,temp2,temp3,temp4,temp5,temp6,temp7;

    for(j = 0; j < 8; j++)
    {	
        B0=ptest[8*j+0];
        B1=ptest[8*j+1];
        B2=ptest[8*j+2];
        B3=ptest[8*j+3];
        B4=ptest[8*j+4];
        B5=ptest[8*j+5];
        B6=ptest[8*j+6];
        B7=ptest[8*j+7];
        
        //step 1 of Loeffler algorithm
        temp0=B0;
        temp1=B4;
        temp2=B2;
        temp3=B6;
        temp4=-B7+B1;
        temp5=B3*sqrt(2);
        temp6=B5*sqrt(2);
        temp7=(B1+B7);
        //step 2 of Loeffler algorithm
        B0=(temp0+temp1);
        B1=(temp0-temp1);
        B2=(temp2*cos(6*pi/16)-temp3*sin(6*pi/16))*sqrt(2);
        B3=(temp2*sin(6*pi/16)+temp3*cos(6*pi/16))*sqrt(2);
        B4=(temp4+temp6);
        B5=(temp7-temp5);
        B6=(temp4-temp6);
        B7=(temp7+temp5);
        //step 3 of Loeffler algorithm
        temp0=(B0+B3);
        temp1=(B1+B2);
        temp2=(B1-B2);
        temp3=(B0-B3);
        temp4=(B4*cos(3*pi/16)-B7*sin(3*pi/16));
        temp5=(B5*cos(1*pi/16)-B6*sin(1*pi/16));
        temp6=(B5*sin(1*pi/16)+B6*cos(1*pi/16));
        temp7=(B4*sin(3*pi/16)+B7*cos(3*pi/16));
        
        output[8*j+0]=change(((temp0+temp7)/2/sqrt(2)));
        output[8*j+1]=change(((temp1+temp6)/2/sqrt(2)));
        output[8*j+2]=change(((temp2+temp5)/2/sqrt(2)));
        output[8*j+3]=change(((temp3+temp4)/2/sqrt(2)));
        output[8*j+4]=change(((temp3-temp4)/2/sqrt(2)));
        output[8*j+5]=change(((temp2-temp5)/2/sqrt(2)));
        output[8*j+6]=change(((temp1-temp6)/2/sqrt(2)));
        output[8*j+7]=change(((temp0-temp7)/2/sqrt(2)));
    }
}

void Fidct3col(int *ptest,int *output)
{
    int j;
    double B0,B1,B2,B3,B4,B5,B6,B7;
    double temp0,temp1,temp2,temp3,temp4,temp5,temp6,temp7;

    for(j = 0; j < 8; j++)
    {	
        B0=ptest[j+0];
        B1=ptest[j+8];
        B2=ptest[j+2*8];
        B3=ptest[j+3*8];
        B4=ptest[j+4*8];
        B5=ptest[j+5*8];
        B6=ptest[j+6*8];
        B7=ptest[j+7*8];
        //step 1 of Loeffler algorithm
        temp0=B0;
        temp1=B4;
        temp2=B2;
        temp3=B6;
        temp4=-B7+B1;
        temp5=B3*sqrt(2);
        temp6=B5*sqrt(2);
        temp7=(B1+B7);
        //step 2 of Loeffler algorithm
        B0=(temp0+temp1);
        B1=(temp0-temp1);
        B2=(temp2*cos(6*pi/16)-temp3*sin(6*pi/16))*sqrt(2);
        B3=(temp2*sin(6*pi/16)+temp3*cos(6*pi/16))*sqrt(2);
        B4=(temp4+temp6);
        B5=(temp7-temp5);
        B6=(temp4-temp6);
        B7=(temp7+temp5);
        //step 3 of Loeffler algorithm
        temp0=(B0+B3);
        temp1=(B1+B2);
        temp2=(B1-B2);
        temp3=(B0-B3);
        temp4=(B4*cos(3*pi/16)-B7*sin(3*pi/16));
        temp5=(B5*cos(1*pi/16)-B6*sin(1*pi/16));
        temp6=(B5*sin(1*pi/16)+B6*cos(1*pi/16));
        temp7=(B4*sin(3*pi/16)+B7*cos(3*pi/16));

        output[j+0]=change(((temp0+temp7)/2/sqrt(2)));
        output[j+8]=change(((temp1+temp6)/2/sqrt(2)));
        output[j+16]=change(((temp2+temp5)/2/sqrt(2)));
        output[j+24]=change(((temp3+temp4)/2/sqrt(2)));
        output[j+32]=change(((temp3-temp4)/2/sqrt(2)));
        output[j+40]=change(((temp2-temp5)/2/sqrt(2)));
        output[j+48]=change(((temp1-temp6)/2/sqrt(2)));
        output[j+56]=change(((temp0-temp7)/2/sqrt(2)));
    }
}

void Fast_IDCT3(int *in_put, int *out_put)
{
	int data[64];
	Fidct3row(in_put,data);
	Fidct3col(data,out_put);
}


///////////////////////////////////////////////////////////////////////////////
//BYTE  ReadByte(char *image_in)//�����ȡ�ֽ�,���Ϊff����������
BYTE  ReadByte()//�����ȡ�ֽ�,���Ϊff����������
{
	BYTE  i;

	i=*(lp++);

	if(i==0xff)
		lp++;

	BitPos=8;
	CurByte=i;

	return i;
}
/*void Initialize_Fast_IDCT()
{
	short i;
	for(i= -512; i<512; i++)
		iclp[i] = (i<-256) ? -256 : ((i>255) ? 255 : i);//�Գ�����Χ����ֵ���д���
}
void idctrow(int * blk)
{
	int x0, x1, x2, x3, x4, x5, x6, x7, x8;
	//intcut
	if (!((x1 = blk[4]<<11) | (x2 = blk[6]) | (x3 = blk[2]) |
		(x4 = blk[1]) | (x5 = blk[7]) | (x6 = blk[5]) | (x7 = blk[3])))
	{
		blk[0]=blk[1]=blk[2]=blk[3]=blk[4]=blk[5]=blk[6]=blk[7]=blk[0]<<3;
		return;
	}
	x0 = (blk[0]<<11) + 128; // for proper rounding in the fourth stage 
	//first stage
	x8 = W7*(x4+x5);
	x4 = x8 + (W1-W7)*x4;
	x5 = x8 - (W1+W7)*x5;
	x8 = W3*(x6+x7);
	x6 = x8 - (W3-W5)*x6;
	x7 = x8 - (W3+W5)*x7;
	//second stage
	x8 = x0 + x1;
	x0 -= x1;
	x1 = W6*(x3+x2);
	x2 = x1 - (W2+W6)*x2;
	x3 = x1 + (W2-W6)*x3;
	x1 = x4 + x6;
	x4 -= x6;
	x6 = x5 + x7;
	x5 -= x7;
	//third stage
	x7 = x8 + x3;
	x8 -= x3;
	x3 = x0 + x2;
	x0 -= x2;
	x2 = (181*(x4+x5)+128)>>8;
	x4 = (181*(x4-x5)+128)>>8;
	//fourth stage
	blk[0] = (x7+x1)>>8;
	blk[1] = (x3+x2)>>8;
	blk[2] = (x0+x4)>>8;
	blk[3] = (x8+x6)>>8;
	blk[4] = (x8-x6)>>8;
	blk[5] = (x0-x4)>>8;
	blk[6] = (x3-x2)>>8;
	blk[7] = (x7-x1)>>8;
}
void idctcol(int * blk)
{
	int x0, x1, x2, x3, x4, x5, x6, x7, x8;
	//intcut
	if (!((x1 = (blk[8*4]<<8)) | (x2 = blk[8*6]) | (x3 = blk[8*2]) |
		(x4 = blk[8*1]) | (x5 = blk[8*7]) | (x6 = blk[8*5]) | (x7 = blk[8*3])))
	{
		blk[8*0]=blk[8*1]=blk[8*2]=blk[8*3]=blk[8*4]=blk[8*5]
			=blk[8*6]=blk[8*7]=iclp[(blk[8*0]+32)>>6];
		return;
	}
	x0 = (blk[8*0]<<8) + 8192;
	//first stage
	x8 = W7*(x4+x5) + 4;
	x4 = (x8+(W1-W7)*x4)>>3;
	x5 = (x8-(W1+W7)*x5)>>3;
	x8 = W3*(x6+x7) + 4;
	x6 = (x8-(W3-W5)*x6)>>3;
	x7 = (x8-(W3+W5)*x7)>>3;
	//second stage
	x8 = x0 + x1;
	x0 -= x1;
	x1 = W6*(x3+x2) + 4;
	x2 = (x1-(W2+W6)*x2)>>3;
	x3 = (x1+(W2-W6)*x3)>>3;
	x1 = x4 + x6;
	x4 -= x6;
	x6 = x5 + x7;
	x5 -= x7;
	//third stage
	x7 = x8 + x3;
	x8 -= x3;
	x3 = x0 + x2;
	x0 -= x2;
	x2 = (181*(x4+x5)+128)>>8;
	x4 = (181*(x4-x5)+128)>>8;
	//fourth stage
	blk[8*0] = iclp[(x7+x1)>>14];
	blk[8*1] = iclp[(x3+x2)>>14];
	blk[8*2] = iclp[(x0+x4)>>14];
	blk[8*3] = iclp[(x8+x6)>>14];
	blk[8*4] = iclp[(x8-x6)>>14];
	blk[8*5] = iclp[(x0-x4)>>14];
	blk[8*6] = iclp[(x3-x2)>>14];
	blk[8*7] = iclp[(x7-x1)>>14];
}*/

int main()
{  

    FILE  *hfjpg;
    DWORD ImgSize;
    DWORD JpegBufSize;
    FILE  * hfbmp;
    void  * hJpegBuf;

    //char * init_out;

    //if((hfjpg=fopen("lena.jpg","rb"))==NULL)
    //if((hfjpg=fopen("jpeg_out_data.jpg","rb"))==NULL)
    if((hfjpg=fopen("F:\\VS\\JPEG\\jpeg_debug\\Doc\\jpeg_out_data.jpg","rb"))==NULL)//��jpg��ʽ��ͼƬ�ļ�
    //if((hfjpg=fopen("F:\\VS\\JPEG\\jpeg_debug\\Doc\\lena_gray.jpg","rb"))==NULL)//��jpg��ʽ��ͼƬ�ļ�
    {
        showerror(FUNC_FILE_ERROR);
        return FALSE;
    }

    fseek(hfjpg,0L,SEEK_END);
    JpegBufSize=ftell(hfjpg);//jpeg�ļ��ĳ���
    fseek(hfjpg,0L,SEEK_SET);//���ص��ļ��Ŀ�ʼ

    if((hJpegBuf=malloc(JpegBufSize))==NULL)//������ʱ�洢�ռ�
    {
        fclose(hfjpg);
        showerror(FUNC_MEMORY_ERROR);
        return FALSE;
    }

    fread((unsigned char  *)hJpegBuf,sizeof( char ),JpegBufSize,hfjpg);//��ȡ�ļ�����
    fclose(hfjpg);

    InitTable();//��ʼ�����������õ��ĸ�������
    //printf("lp=%d \n",lp);
    if(InitTag(hJpegBuf)!=FUNC_OK)//�Ӹ�����Ƕ��еõ���������ֵ
    {
        
        free(hJpegBuf);//�ͷŴ洢�ռ�
        showerror(FUNC_FILE_ERROR);
        return FALSE;
    }

    //printf("lp1=%d \n",lp);
    bi.biSize=(DWORD)sizeof(BITMAPINFOHEADER);
    bi.biWidth=(LONG)(ImgWidth);
    bi.biHeight=(LONG)(ImgHeight);
    bi.biPlanes=1;
    bi.biBitCount=24;//bmp��ʽ�п��ܱ�����RGB�����������ʴ�ֵ����Ϊ3�ֽڼ�24bits
    bi.biClrUsed=0;
    bi.biClrImportant=0;
    bi.biCompression=BI_RGB;
    NumColors=0;
    //------------------��ӡ���bmpͼ��������Ϣ---------------------------------
    printf("bi.biWidth is %ld\n",bi.biWidth);
    printf("bi.biBitCount is %ld\n",bi.biBitCount);
    LineBytes=(DWORD)WIDTHBYTES(bi.biWidth*bi.biBitCount);//ÿ���ֽ���
    printf("LineBytes is %ld\n",LineBytes);
    ImgSize=(DWORD)LineBytes*bi.biHeight;//����ͼ���ݲ��ֵ��ֽ���
    printf("size is %ld\n",ImgSize);

    bf.bfType=0x4d42;
    bf.bfSize=sizeof(BITMAPFILEHEADER)+sizeof(BITMAPINFOHEADER)+ImgSize;
    bf.bfOffBits=54;

    printf("size is %ld\n",ImgSize);
    if((hImgData=(char*)malloc(ImgSize))==NULL)
    {
        free(hJpegBuf);
        showerror(FUNC_MEMORY_ERROR);
        return FALSE;
    }

    lpPtr=hImgData;
    if((SampRate_Y_H==0)||(SampRate_Y_V==0))
    {
        free(hJpegBuf);
        free(hImgData);
        hImgData=NULL;
        showerror(FUNC_FORMAT_ERROR);
        return FALSE ;
    }

    if( Decode(hImgData)==FUNC_OK)//����jpeg
    {
        
        //if((hfbmp=fopen("test.bmp","wb"))==NULL)//��Ҫ�洢�����bmp�ļ�
        if((hfbmp=fopen("F:\\VS\\JPEG\\jpeg_debug\\Doc\\test.bmp","wb"))==NULL)//��Ҫ�洢�����bmp�ļ�
        {
            showerror(FUNC_FILE_ERROR);
            return FALSE;
        }
        
        
        fwrite((char *)&bf,sizeof(BITMAPFILEHEADER),1,hfbmp); //д���ļ�ͷ
        fwrite((char *)&bi,sizeof(BITMAPINFOHEADER),1,hfbmp);//д��bmp��Ϣͷ
        fwrite((char *)hImgData,sizeof(char),ImgSize,hfbmp);//д��bmpͼ������
        fclose(hfbmp);
        free(hJpegBuf);
        return TRUE;
    }
    else
    {
        free(hJpegBuf);
        free(hImgData);
        hImgData=NULL;
        showerror(FUNC_FILE_ERROR);
        return FALSE;
    }
    return 0;
}


