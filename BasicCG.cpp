#include<iostream>
#include<cstdio>
#include<cstring>
#include<cmath>
#include<algorithm>
#include<cstdlib>
#include<vector>
using namespace std;
#define eps (1e-9)
#define NN 1010

const double pi=acos(-1.0);
double degtorad(double deg){return deg/180.0*pi;}
double radtodeg(double rad){return rad*180.0/pi;}

double fabs(double d){return d<0?-d:d;}//特别注意写法，防止-0.00
int dcmp(double d){return (fabs(d)<eps)?0:(d>0?1:-1);}

struct pt{
    double x,y;
    pt(){}
    pt(double x,double y):x(x),y(y){};
    pt operator +(pt b){return pt(x+b.x,y+b.y);}
    pt operator -(pt b){return pt(x-b.x,y-b.y);}
    pt operator *(double k){return pt(x*k,y*k);}
    pt operator /(double k){return pt(x/k,y/k);} //k!=0
    double operator *(pt b){return x*b.y-b.x*y;} //cross sin<a,b>
    double operator %(pt b){return x*b.x+y*b.y;} //dot cos<a,b>
    bool operator <(const pt &b)const{return dcmp(y-b.y)==0?x<b.x:y<b.y;}
    bool operator ==(const pt &b)const{return dcmp(x-b.x)==0&&dcmp(y-b.y)==0;}
};
double cross(pt a,pt b,pt c){return (b-a)*(c-a);}
double dot(pt a,pt b,pt c){return (b-a)%(c-a);}
double length(pt a){return sqrt(a.x*a.x+a.y*a.y);}
double angle(pt a,pt b){return acos(a%b/length(a)/length(b));}
double area2(pt a,pt b,pt c){return (b-a)*(c-a);}//abc有向面积两倍

pt rotate(pt a,double rad){//绕原点逆时针旋转
    return pt(a.x*cos(rad)-a.y*sin(rad),a.x*sin(rad)+a.y*cos(rad));
}

pt normal(pt a){//求单位法线，左转90°规格化
    double l=length(a);
    return pt(-a.y/l,a.x/l);
}

double disptol(pt p,pt a1,pt a2){//点到直线距离,两直线距离取一点即可
    pt v1=a2-a1,v2=p-a1;
    return fabs(v2*v1/length(v1));
}

double disptos(pt p,pt a1,pt a2){//点到线段距离
    if (a1==a2) return length(a1-a2);
    pt v1=a2-a1,v2=p-a1,v3=p-a2;
    if (dcmp(v1%v2)<0) return length(v2);
    else if (dcmp(v1%v3)>0) return length(v3);
    else return fabs(v2*v1/length(v1));
}

int pons(pt p,pt a1,pt a2){//点在线段上(含端点),0,1, 在直线上只需要叉积等于0即可
    return dcmp((a1-p)*(a2-p))==0&&dcmp((a1-p)%(a2-p))<=0;
}

int scross1(pt a,pt b,pt c,pt d){//线段规范相交，不计端点,0,1
    return dcmp((b-a)*(c-a))*dcmp((b-a)*(d-a))==-1&&
           dcmp((d-c)*(a-c))*dcmp((d-c)*(b-c))==-1;
}

int scross2(pt a,pt b,pt c,pt d){//线段相交含端点 0,1,-1
    if (scross1(a,b,c,d)) return 1;//规范相交
    if (pons(c,a,b)||pons(d,a,b)||pons(a,c,d)||pons(b,c,d)) return -1;//在端点相交
    return 0;//不相交
}

int parallel(pt u1, pt u2, pt v1, pt v2) //直线平行 u1u2 // v1v2
{
    return fabs((u2-u1)*(v2-v1))<eps;
}

pt intersection(pt u1, pt u2, pt v1, pt v2) //直线交点 u1u2 X v1v2 需先判断是否平行！！
{
    double t=((u1.x-v1.x)*(v1.y-v2.y)-(u1.y-v1.y)*(v1.x-v2.x))
            /((u1.x-u2.x)*(v1.y-v2.y)-(u1.y-u2.y)*(v1.x-v2.x));
    return pt(t*(u2.x-u1.x)+u1.x,t*(u2.y-u1.y)+u1.y);
}


pt getinter(pt a,pt b,pt c,pt d){//ab cd直线交点,线段需先判断是否相交
    double s1=(b-a)*(c-a);
    double s2=(b-a)*(d-a);
    pt p;
    p.x=(c.x*s2-d.x*s1)/(s2-s1);
    p.y=(c.y*s2-d.y*s1)/(s2-s1);
    return p;
}

double getarea(pt p[],int n){//多边形有向面积，点有序，p[0..n-1]，顺时针小于零
    double res=0;
    p[n]=p[0];
    for(int i=0;i<n;i++) res+=p[i]*p[i+1]; //cross(O,p[i],p[i+1]);
    return res/2.0;
}
pt getcentroid(pt p[],int n){ //求重心 p[0..n-1];
    double tx=0,ty=0,tc;
    double a=getarea(p,n);
    p[n]=p[0];
    for(int i=0;i<n;i++)  {
        tc=p[i]*p[i+1];
        tx=tx+(p[i].x+p[i+1].x)*tc;
        ty=ty+(p[i].y+p[i+1].y)*tc;
    }
    return pt(tx/(6.0*a),ty/(6.0*a));
}

int pinpoly(pt a,pt p[],int n){//点与多边形位置关系
    int wn=0;
    p[n]=p[0];
    for(int i=0;i<n;++i){
        if (pons(a,p[i],p[i+1])) return -1;//边界
        int k=dcmp((p[i+1]-p[i])*(a-p[i]));
        int d1=dcmp(p[i].y-a.y);
        int d2=dcmp(p[i+1].y-a.y);
        if (k>0&&d1<=0&&d2>0) wn++;
        if (k<0&&d2<=0&&d1>0) wn--;
    }
    if (wn!=0) return 1;//内部
    return 0;//外部
}
/*
struct line{
    point p;
    point v;
    line(pt ,pt v):p(p),v(v)){}
    pt getpt(double l){return p+v*l;}
}
*/
//圆--------------------------
struct circle{
    pt p;
    double r;
    circle(){};
    circle(pt p,double r):p(p),r(r){}
    pt getpt(double a){
        return pt(p.x+cos(a)*r,p.y+sin(a)*r);
    }
};
//圆与直线交点
int linsc(pt a1,pt a2,circle c,double &t1,double &t2,vector<pt>& sol){
    pt v=a2-a1;
    double a=v.x,b=a1.x-c.p.x,d=v.y,f=a1.y-c.p.y;
    double aa=a*a+d*d,bb=2*(a*b+d*f),cc=b*b+f*f-c.r*c.r;
    double delta=bb*bb-4*aa*cc;
    if (dcmp(delta)<0) return 0;//相离
    if (dcmp(delta)==0){//相切
        t1=t2=-bb/(2*aa);sol.push_back(a1+v*t1);
        return 1;
    }
    //相交
    t1=(-bb-sqrt(delta))/(2*aa);sol.push_back(a1+v*t1);
    t2=(-bb+sqrt(delta))/(2*aa);sol.push_back(a1+v*t2);
    return 2;
}
//两圆交点
int cinsc(circle c1,circle c2,vector<pt> &sol){
    double d=length(c1.p-c2.p);
    if (dcmp(d)==0){
        if (dcmp(c1.r-c2.r)==0) return -1;//重合
        return 0;//包含
    }
    if (dcmp(c1.r+c2.r-d)<0) return 0;
    if (dcmp(fabs(c1.r-c2.r)-d)>0) return 0;
    double a=atan2(c1.p.y-c2.p.y,c1.p.x-c2.p.x);
    double da=acos((c1.r*c1.r+d*d-c2.r*c2.r)/(2*c1.r*d));

    pt p1=c1.getpt(a-da),p2=c1.getpt(a+da);
    sol.push_back(p1);
    if (p1==p2) return 1;
    sol.push_back(p2);
    return 2;
}
//过点圆切线 0,1,2
int gettangentpc(pt p,circle c,vector<pt> v){
    pt u=c.p-p;
    double dist=length(u);
    if (dist<c.r) return 0;
    else if (dcmp(dist-c.r)==0) {
        v.push_back(rotate(u,pi/2));
        return 1;
    }
    else{
        double ang=asin(c.r/dist);
        v.push_back(rotate(u,-ang));
        v.push_back(rotate(u,ang));
        return 2;
    }
}

//圆与圆切线 a[],b[],存放对应切线的切点
int gettangentcc(circle c1,circle c2,pt *a,pt *b){
    int cnt=0;
    if (c1.r<c2.r){swap(c1,c2);swap(a,b);}
    double d2=length(c1.p-c2.p);
    double rdiff=c1.r-c2.r;
    double rsum=c1.r+c2.r;
    if (dcmp(d2-rdiff)<0) return 0;//内含，无切线

    double base=atan2(c1.p.y-c2.p.y,c1.p.x-c2.p.x);
    if (dcmp(d2)==0&&c1.r==c2.r) return -1;//重合 无数条切线
    if (dcmp(d2-rdiff)==0){//内切，一条切线
        a[cnt]=c1.getpt(base);b[cnt]=c2.getpt(base);cnt++;
        return 1;
    }
    //求外切线
    double ang=acos((c1.r-c2.r)/d2);
    a[cnt]=c1.getpt(base+ang);b[cnt]=c2.getpt(base+ang);cnt++;
    a[cnt]=c1.getpt(base-ang);b[cnt]=c2.getpt(base-ang);cnt++;
    if (dcmp(d2-rsum)==0){//两圆外切，一条内切线
        a[cnt]=c1.getpt(base);b[cnt]=c2.getpt(pi+base);cnt++;
    }
    else if (dcmp(d2-rsum)>0){//两圆相离，两条内切线
        ang=acos((c1.r+c2.r)/d2);
        a[cnt]=c1.getpt(base+ang);b[cnt]=c2.getpt(pi+base+ang);cnt++;
        a[cnt]=c1.getpt(base-ang);b[cnt]=c2.getpt(pi+base-ang);cnt++;
    }
    return cnt;
}
//外接圆，垂直平分线交点
circle getcircumcircle(pt a,pt b,pt c){
    circle ret;
    pt p1=(a+b)/2,p2=(a+b)/2+rotate(b-a,pi/2);
    pt p3=(c+b)/2,p4=(c+b)/2+rotate(b-c,pi/2);
    ret.p=getinter(p1,p2,p3,p4);
    ret.r=length(ret.p-a);
    return ret;
}
//内切圆，角平分线交点
circle getincircle(pt a,pt b,pt c){
    circle ret;
    double m=atan2(b.y-a.y,b.x-a.x),n=atan2(c.y-a.y,c.x-a.x);
    pt ua,ub,va,vb;
    ua=a;
    ub=ua+pt(cos((n+m)/2),sin((n+m)/2));
    va=b;
    m=atan2(a.y-b.y,a.x-b.x),n=atan2(c.y-b.y,c.x-b.x);
    vb=va+pt(cos((n+m)/2),sin((n+m)/2));
    ret.p=getinter(ua,ub,va,vb);
    ret.r=disptol(ret.p,a,b);
    return ret;
}


//----------------------圆---------------------------
//凸包 andrew O(nlogn))------------------------------------
pt p[NN];
int cp[NN];

int convex(pt p[],int n,int cp[]){
    sort(p,p+n);
    int i,up,cn=0;      //凸包上总点数cn，点的编号存放在cp[0..cn-1]中。
    for (i=0;i<n;i++){
        while ( cn>1 && cross(p[cp[cn-2]],p[cp[cn-1]],p[i])<eps) cn--;//<eps不记录共线点
        cp[cn++]=i;                                                  //<-eps记录共线点,必须去重点
    }
    up=cn;
    for (i=n-1;i>=0;i--){
        while (cn>up && cross(p[cp[cn-2]],p[cp[cn-1]],p[i])<eps) cn--;
        cp[cn++]=i;
    }
    if (n>1) cn--;
    return cn;
}
//旋转卡壳求最远两点距离^2 O(n)
double getdis2(pt a,pt b){return (a.x-b.x)*(a.x-b.x)+(a.y-b.y)*(a.y-b.y);}
double getdp(pt p[],int cp[],int cn){
     int i,j=0,cnt=0;
     double tmp1,tmp2,tmp,ma=0;
     cp[cn]=cp[0];//注意
     for(i=0;i<cn;i++){
         tmp1=fabs(area2(p[cp[i]],p[cp[i+1]],p[cp[j]]));
         for(;cnt<=2*cn;j++,cnt++){
            if (j>=cn) j=0;
            tmp=getdis2(p[cp[i]],p[cp[j]]);if (tmp>=ma) ma=tmp;
            tmp=getdis2(p[cp[i+1]],p[cp[j]]);if (tmp>=ma) ma=tmp;
            tmp2=fabs(area2(p[cp[i]],p[cp[i+1]],p[cp[j]]));
            if (tmp2<tmp1-eps) break;
            else tmp1=tmp2;
         }
         j=(j==0?cn-1:j-1);  cnt--;
     }
     return ma;
}

//-------------凸包--------------
int gcd(int a,int b){return b==0?(a==0?1:a):gcd(b,a%b);}

int main(){
    int i,flag,tn,ans;
    double a;
    while(1){
        flag=0;
        for(i=0;i<3;++i){
            scanf("%lf%lf",&p[i].x,&p[i].y);
            if (p[i].x!=0||p[i].y!=0) flag=1;
        }
        if (flag==0) break;
        p[3]=p[0];
        tn=0;
        for(i=0;i<3;++i){
            tn+=gcd((int)(fabs(p[i+1].y-p[i].y)+0.5),(int)(fabs(p[i+1].x-p[i].x)+0.5));
        }
        a=fabs(getarea(p,3));
        //printf("   %d %lf\n",tn,a);
        ans=(int)(a+eps)-tn/2+1;
        printf("%d\n",ans);
    }
    return 0;
}








