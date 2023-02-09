#include <iostream>
#include <cmath>
#include <list>
#include<stdio.h>
#include <string>
#include <chrono>
#include <ext/hash_map>
#include "main.h"
using namespace std;
using namespace __gnu_cxx;

//установка констант
Dstar::Dstar() {
    maxSteps = 800000;  // расширения узлов, прежде чем мы сдадимся
    C1       = 1;      // стоимость невидимой ячейки
}

//Возвращает хэш-код ключа для состояния u, который используется для сравнения
// состояние, которое было обновлено
float Dstar::keyHashCode(state u) {
    return (float)(u.k.first + 1193*u.k.second);//1193
}

//Возвращает значение true, если состояние u находится
// в открытом списке или нет,
// проверяя, есть ли оно в хэш-таблице.
bool Dstar::isValid(state u) {
    ds_oh::iterator cur = openHash.find(u);
    if (cur == openHash.end()) return false;
    if (!close(keyHashCode(u), cur->second)) return false;
    return true;
}
//Возвращает путь, созданный replan()
list<state> Dstar::getPath() {
    return path;
}

//возвращает значение true, если ячейка занята (недоступна для обхода),
//в противном случае значение false. непроходимые отмечены стоимостью < 0.
bool Dstar::occupied(state u) {

    ds_ch::iterator cur = cellHash.find(u);

    if (cur == cellHash.end()) return false;
    return (cur->second.cost < 0);
}

//Инициализация d star начинается с координат начала и цели, остальное в соответствии
//[S. Koenig, 2002]
void Dstar::init(int sX, int sY, int gX, int gY) {

    cellHash.clear();
    path.clear();
    openHash.clear();
    while(!openList.empty()) openList.pop();

    k_m = 0;

    s_start.x = sX;
    s_start.y = sY;
    s_goal.x  = gX;
    s_goal.y  = gY;

    cellInfo tmp;
    tmp.g = tmp.rhs =  0;
    tmp.cost = C1;

    cellHash[s_goal] = tmp;

    tmp.g = tmp.rhs = heuristic(s_start,s_goal);
    tmp.cost = C1;
    cellHash[s_start] = tmp;
    s_start = calculateKey(s_start);
    s_last = s_start;
}
//Проверяет, есть ли ячейка в хэш-таблице, если нет, то добавляет ее в нее
void Dstar::makeNewCell(state u) {
    if (cellHash.find(u) != cellHash.end()) return;
    cellInfo tmp;
    tmp.g       = tmp.rhs = heuristic(u,s_goal);
    tmp.cost    = C1;
    cellHash[u] = tmp;
}
//Возвращает значение G для состояния u.
double Dstar::getG(state u) {
    if (cellHash.find(u) == cellHash.end())
        return heuristic(u,s_goal);
    return cellHash[u].g;
}

//Возвращает значение rhs для состояния u.
double Dstar::getRHS(state u) {

    if (u == s_goal) return 0;
    if (cellHash.find(u) == cellHash.end())
        return heuristic(u,s_goal);
    return cellHash[u].rhs;
}

//Задает значение G для состояния u
void Dstar::setG(state u, double g) {

    makeNewCell(u);
    cellHash[u].g = g;
}
//Задает значение rhs для состояния u
double Dstar::setRHS(state u, double rhs) {

    makeNewCell(u);
    cellHash[u].rhs = rhs;

}

//Возвращает 8-полосное расстояние между состоянием a и состоянием b.
double Dstar::eightCondist(state a, state b) {
    double temp;
    double min = fabs(a.x - b.x);
    double max = fabs(a.y - b.y);
    if (min > max) {
        double temp = min;
        min = max;
        max = temp;
    }
    return ((M_SQRT2-1.0)*min + max);
}


/* Согласно [S. Koenig, 2002], за исключением 2 основных модификаций:
* 1. Мы прекращаем планирование после нескольких шагов, "maxsteps" мы делаем это
* потому что этот алгоритм может планировать вечно, если начало
* окруженный препятствиями.
* 2. Мы лениво удаляем состояния из открытого списка, чтобы нам никогда не приходилось
* перебирать его.
 */
int Dstar::computeShortestPath() {
    list<state> s;
    list<state>::iterator i;

    if (openList.empty()) return 1;

    int k=0;
    while ((!openList.empty()) &&
           (openList.top() < (s_start = calculateKey(s_start))) ||
           (getRHS(s_start) != getG(s_start))) {

        if (k++ > maxSteps) {
            fprintf(stderr, "At maxsteps\n");
            return -1;
        }
        state u;
        bool test = (getRHS(s_start) != getG(s_start));

        // ленивое удаление
        while(1) {
            if (openList.empty()) return 1;
            u = openList.top();
            openList.pop();
            if (!isValid(u)) continue;
            if (!(u < s_start) && (!test)) return 2;
            break;
        }
        ds_oh::iterator cur = openHash.find(u);
        openHash.erase(cur);

        state k_old = u;

        if (k_old < calculateKey(u)) { // u устарел
            insert(u);
        } else if (getG(u) > getRHS(u)) { // нуждается в обновлении (стало лучше)
            setG(u,getRHS(u));
            getPred(u,s);
            for (i=s.begin();i != s.end(); i++) {
                updateVertex(*i);
            }
        } else {   // g <= rhs, состояние ухудшилось
            setG(u,INFINITY);
            getPred(u,s);
            for (i=s.begin();i != s.end(); i++) {
                updateVertex(*i);
            }
            updateVertex(u);
        }
    }
    return 0;
}

//Возвращает значение true, если x и y находятся в пределах 10E-5, в противном случае значение false

bool Dstar::close(double x, double y) {

    if (isinf(x) && isinf(y)) return true;
    return (fabs(x-y) < 0.00001);
}

void Dstar::updateVertex(state u) {
    list<state> s;
    list<state>::iterator i;

    if (u != s_goal) {
        getSucc(u,s);
        double tmp = INFINITY;
        double tmp2;

        for (i=s.begin();i != s.end(); i++) {
            tmp2 = getG(*i) + cost(u,*i);
            if (tmp2 < tmp) tmp = tmp2;
        }
        if (!close(getRHS(u),tmp)) setRHS(u,tmp);
    }
    if (!close(getG(u),getRHS(u))) insert(u);
}

//Добавляем состояние u в открытый список и открытый хэш.
void Dstar::insert(state u) {

    ds_oh::iterator cur;
    float csum;
    u    = calculateKey(u);
    cur  = openHash.find(u);
    csum = keyHashCode(u);
    openHash[u] = csum;
    openList.push(u);
}

//Удаляет состояние u из openHash. Состояние удалено из
//openList лениво (в плане) что бы сэкономить время.
void Dstar::remove(state u) {

    ds_oh::iterator cur = openHash.find(u);
    if (cur == openHash.end()) return;
    openHash.erase(cur);
}

//Евклидова стоимость между состоянием a и состоянием b.
double Dstar::trueDist(state a, state b) {

    float x = a.x-b.x;
    float y = a.y-b.y;
    return sqrt(x*x + y*y);

}

 /* Само собой разумеется, что эвристика,
   которую мы используем, - это расстояние в 8 направлениях
 * масштабируется на константу C1 (должно быть установлено значение больше <= min cost).
 */
double Dstar::heuristic(state a, state b) {
    return eightCondist(a,b)*C1;
}

//Согласно [S. Кениг, 2002]
state Dstar::calculateKey(state u) {

    double val = fmin(getRHS(u),getG(u));
    u.k.first  = val + heuristic(u,s_start) + k_m;
    u.k.second = val;
    return u;
}

/*
 * Возвращает стоимость перехода из состояния a в состояние b. Это может быть
 * либо стоимость переезда из состояния a  в состояние b,мы выбрали первое
 * Это также стоимость в 8 сторон
 */
double Dstar::cost(state a, state b) {

    int xd = fabs(a.x-b.x);
    int yd = fabs(a.y-b.y);
    double scale = 1;

    if (xd + yd > 1) scale = M_SQRT2;

    if (cellHash.count(a) == 0) return scale*C1;
    return scale*cellHash[a].cost;

}

//Согласно [S. Кениг, 2002]
void Dstar::updateCell(int x, int y, double val) {

    state u;
    u.x = x;
    u.y = y;

    if ((u == s_start) || (u == s_goal)) return;

    makeNewCell(u);
    cellHash[u].cost = val;

    updateVertex(u);
}

/*
 * Возвращает список состояний-преемников для состояния u, поскольку это
 * 8-полосный график этот список содержит все соседние ячейки. Если не
 * ячейка занята, и в этом случае у нее нет преемников.
 */
void Dstar::getSucc(state u,list<state> &s) {

    s.clear();
    u.k.first  = -1;
    u.k.second = -1;

    if (occupied(u)) return;
    u.x += 1;
    s.push_front(u);
    u.y += 1;
    s.push_front(u);
    u.x -= 1;
    s.push_front(u);
    u.x -= 1;
    s.push_front(u);
    u.y -= 1;
    s.push_front(u);
    u.y -= 1;
    s.push_front(u);
    u.x += 1;
    s.push_front(u);
    u.x += 1;
    s.push_front(u);

}

/*
 * Возвращает список всех состояний-предшественников для состояния u.
 * Поскольку это для 8-полосного связного графа, список содержит все
   соседи для состояния u.
   Занятые соседи не добавляются в список.
 */
void Dstar::getPred(state u,list<state> &s) {

    s.clear();
    u.k.first  = -1;
    u.k.second = -1;

    u.x += 1;
    if (!occupied(u)) s.push_front(u);
    u.y += 1;
    if (!occupied(u)) s.push_front(u);
    u.x -= 1;
    if (!occupied(u)) s.push_front(u);
    u.x -= 1;
    if (!occupied(u)) s.push_front(u);
    u.y -= 1;
    if (!occupied(u)) s.push_front(u);
    u.y -= 1;
    if (!occupied(u)) s.push_front(u);
    u.x += 1;
    if (!occupied(u)) s.push_front(u);
    u.x += 1;
    if (!occupied(u)) s.push_front(u);

}

//Обновите позицию робота, это не приведет к принудительному воспроизведению.
void Dstar::updateStart(int x, int y) {

    s_start.x = x;
    s_start.y = y;

    k_m += heuristic(s_last,s_start);

    s_start = calculateKey(s_start);
    s_last  = s_start;
}

/*
 Это своего рода взлом, чтобы изменить положение цели,
 мы сначала сохраняем все непустые ячейки на карте,
 очищаем карту, перемещаем цель и повторно добавляем все непустые ячейки.
 Поскольку большинство этих ячеек не находятся между началом и целью,
 это, по-видимому, не слишком влияет на производительность.
 Кроме того, это освобождает значительную часть памяти, которую мы, скорее всего, больше не используем.
 */
void Dstar::updateGoal(int x, int y) {

    list< pair<ipoint2, double> > toAdd;
    pair<ipoint2, double> tp;

    ds_ch::iterator i;
    list< pair<ipoint2, double> >::iterator kk;

    for(i=cellHash.begin(); i!=cellHash.end(); i++) {
        if (!close(i->second.cost, C1)) {
            tp.first.x = i->first.x;
            tp.first.y = i->first.y;
            tp.second = i->second.cost;
            toAdd.push_back(tp);
        }
    }

    cellHash.clear();
    openHash.clear();

    while(!openList.empty())
        openList.pop();

    k_m = 0;

    s_goal.x  = x;
    s_goal.y  = y;

    cellInfo tmp;
    tmp.g = tmp.rhs =  0;
    tmp.cost = C1;

    cellHash[s_goal] = tmp;

    tmp.g = tmp.rhs = heuristic(s_start,s_goal);
    tmp.cost = C1;
    cellHash[s_start] = tmp;
    s_start = calculateKey(s_start);

    s_last = s_start;

    for (kk=toAdd.begin(); kk != toAdd.end(); kk++) {
        updateCell(kk->first.x, kk->first.y, kk->second);
    }

}


/* Обновляет затраты для всех ячеек и вычисляет кратчайший путь к
цели. Возвращает значение true, если путь найден, в противном случае значение false. Путь
вычисляется путем выполнения жадного поиска по значениям cost+g в каждой
ячейке. Чтобы обойти проблему, связанную с тем, что робот выбирает
путь, который находится под углом около 45 градусов к цели, мы разрываем связи, основанные на
метрике евклида (состояние, цель) + евклидово (состояние, начало).
 */

bool Dstar::replan() {

    path.clear();
    int res = computeShortestPath();

    if (res < 0) {
        fprintf(stderr, "НЕТ ПУТИ К ЦЕЛИ\n");
        return false;
    }
    list<state> n;
    list<state>::iterator i;

    state cur = s_start;

    if (isinf(getG(s_start))) {
        fprintf(stderr, "НЕТ ПУТИ К ЦЕЛИ\n");
        return false;
    }

    while(cur != s_goal) {

        path.push_back(cur);
        getSucc(cur, n);

        if (n.empty()) {
            fprintf(stderr, "НЕТ ПУТИ К ЦЕЛИ\n");
            return false;
        }

        double cmin = INFINITY;
        double tmin;
        state smin;

        for (i=n.begin(); i!=n.end(); i++) {

            //if (occupied(*i)) continue;
            double val  = cost(cur,*i);
            double val2 = trueDist(*i,s_goal) + trueDist(s_start,*i); // ((Евклидова) стоимость достижения цели + стоимость прогнозирования
            val += getG(*i);

            if (close(val,cmin)) {
                if (tmin > val2) {
                    tmin = val2;
                    cmin = val;
                    smin = *i;
                }
            } else if (val < cmin) {
                tmin = val2;
                cmin = val;
                smin = *i;
            }
        }
        n.clear();
        cur = smin;
    }
    path.push_back(s_goal);
    return true;
}

int main() {
    Dstar *dstar = new Dstar();
    list<state> mypath;

    int n1=15;
    int arr[n1];
    auto begin = std::chrono::steady_clock::now();
    for (int j=0;j<20;j++)
    {

        char in_f[400];

        sprintf(in_f,"tes/%i/in.txt",j);
        FILE* in_file= fopen(in_f,"r");

        for (int i = 0; i < 20; i++){
            fscanf(in_file, "%d,", &arr[i] );
        }

        dstar->init(arr[0],arr[1],arr[2],arr[3]); //начало на (0,0) и цель на (10,5)
        dstar->updateCell(arr[4],arr[5],-1);     // ячейка (3,4) недоступной для обхода
        dstar->updateCell(arr[6],arr[7],42.432);// ячейка (2,2), чтобы иметь стоимость 42,432

        dstar->replan();               // спланировать путь
        mypath = dstar->getPath();     // получить путь
        dstar->updateCell(arr[8],arr[9],arr[10]);


        dstar->updateStart(arr[11],arr[12]);      // установите начало на (0,0), а цель на (10,5)
        dstar->replan();               // спланируйте путь
        mypath = dstar->getPath();     // извлекать путь


        dstar->updateGoal(arr[13],arr[14]);        // переместить цель на (0,1)
        dstar->replan();               // спланируйте путь
        mypath = dstar->getPath();     // извлекать путь

        int res = dstar->computeShortestPath();
        char out_f[400];
        sprintf(out_f,"tes/%i/out.txt",j);
        FILE* file= fopen(out_f,"w");
        fprintf(file ,
                "computeShortestPath: %d,\n"
                "openList.size: %d,\n"
                "openHash.size: %d\n"
                "openList.top.k.first_second: [%f %f]\n"
                "s_start.k.first_second: [%f %f]\n"
                "getRHS_getG: (%f,%f)\n",
                res,
                dstar->openList.size(),//кол-во оставшихся вершин в списке
                dstar->openHash.size(),
                dstar->openList.top().k.first,//первая вершина в открытом списке
                dstar->openList.top().k.second,//последняя вершина в открытом списке
                dstar->s_start.k.first,//1 значение начальной вершины
                dstar->s_start.k.second,//2 значение начальной вергины
                dstar->getRHS(dstar->s_start),//правое значение
                dstar->getG(dstar->s_start));//значение G


        auto end = std::chrono::steady_clock::now();
        auto time = std::chrono::duration_cast<std::chrono::milliseconds>(end - begin);
        //std::cout <<"Test:"<<j<< " the time: " << time.count() << " ms\n";
        //cout<<time.count()<<'\n';
        fclose(file);
        fclose(in_file);
    }

    return 0;
}