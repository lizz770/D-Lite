#include <iostream>
#include <cmath>
#include <queue>
#include <list>
#include<cstdio>
#include <string>
#include <chrono>
#include <ext/hash_map>

using namespace std;
using namespace __gnu_cxx;

class state {
public:
    int x;
    int y;
    pair<double,double> k;

    bool operator == (const state &s2) const {
        return ((x == s2.x) && (y == s2.y));
    }

    bool operator != (const state &s2) const {
        return ((x != s2.x) || (y != s2.y));
    }

    bool operator > (const state &s2) const {
        if (k.first-0.00001 > s2.k.first) return true;
        else if (k.first < s2.k.first-0.00001) return false;
        return k.second > s2.k.second;
    }

    bool operator <= (const state &s2) const {
        if (k.first < s2.k.first) return true;
        else if (k.first > s2.k.first) return false;
        return k.second < s2.k.second + 0.00001;
    }


    bool operator < (const state &s2) const {
        if (k.first + 0.000001 < s2.k.first) return true;
        else if (k.first - 0.000001 > s2.k.first) return false;
        return k.second < s2.k.second;
    }

};
struct ipoint2 {
    int x,y;
};
//информация о ячейке
struct cellInfo {

    double g;
    double rhs;
    double cost;

};

class state_hash {
public:
    size_t operator()(const state &s) const {
        return s.x + 34245*s.y;
    }
};


typedef priority_queue<state, vector<state>, greater<state> > ds_pq;
typedef hash_map<state,cellInfo, state_hash, equal_to<state> > ds_ch;
typedef hash_map<state, float, state_hash, equal_to<state> > ds_oh;


class Dstar {

public:

    Dstar();
    void   init(int sX, int sY, int gX, int gY);
    void   updateCell(int x, int y, double val);
    void   updateStart(int x, int y);
    void   updateGoal(int x, int y);
    bool   replan();

    list<state> getPath();

private:

    list<state> path;

    double C1;
    double k_m;
    state s_start, s_goal, s_last;
    int maxSteps;

    ds_pq openList;
    ds_ch cellHash;
    ds_oh openHash;

    bool   close(double x, double y);
    void   makeNewCell(state u);
    double getG(state u);
    double getRHS(state u);
    void   setG(state u, double g);
    double setRHS(state u, double rhs);
    double eightCondist(state a, state b);
    int    computeShortestPath();
    void   updateVertex(state u);
    void   insert(state u);
    void   remove(state u);
    double trueDist(state a, state b);
    double heuristic(state a, state b);
    state  calculateKey(state u);
    void   getSucc(state u, list<state> &s);
    void   getPred(state u, list<state> &s);
    double cost(state a, state b);
    bool   occupied(state u);
    bool   isValid(state u);
    float  keyHashCode(state u);
};


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
//Returns true if x and y are within 10E-5, false otherwise

bool Dstar::close(double x, double y) {

    if (isinf(x) && isinf(y)) return true;
    return (fabs(x-y) < 0.00001);
}

//Согласно [S. Кениг, 2002]
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
//Inserts state u into openList and openHash.
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
 * Returns a list of successor states for state u, since this is an
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
    FILE *file;
    file=fopen("out.txt","w+t");
    fprintf(file ,"res: %d ols: %d ohs: %d tk: [%f %f] sk: [%f %f] sgr: (%f,%f)\n",res,openList.size(), openHash.size(), openList.top().k.first, openList.top().k.second, s_start.k.first, s_start.k.second, getRHS(s_start), getG(s_start));
    printf("res: %d ols: %d ohs: %d tk: [%f %f] sk: [%f %f] sgr: (%f,%f)\n",res,openList.size(), openHash.size(), openList.top().k.first, openList.top().k.second, s_start.k.first, s_start.k.second, getRHS(s_start), getG(s_start));
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
    FILE *file;
    file = fopen("test1.txt", "r");

    int n1;
    int arr[n1];
    for (int i = 0; i < n1; i++){
        fscanf(file, "%d,", &arr[i] );
    }
    auto begin = std::chrono::steady_clock::now();
    dstar->init(arr[0],arr[1],arr[2],arr[3]); // set start to (0,0) and goal to (10,5)
    dstar->updateCell(arr[4],arr[5],-1);     // set cell (3,4) to be non traversable
    dstar->updateCell(arr[6],arr[7],42.432); // set set (2,2) to have cost 42.432

    dstar->replan();               // plan a path
    mypath = dstar->getPath();     // retrieve path

    dstar->updateStart(arr[8],arr[9]);      // move start to (10,2)
    dstar->replan();               // plan a path
    mypath = dstar->getPath();     // retrieve path

    dstar->updateGoal(arr[10],arr[11]);        // move goal to (0,1)
    dstar->replan();               // plan a path
    mypath = dstar->getPath();     // retrieve path
    auto end = std::chrono::steady_clock::now();
    auto elapsed_ms = std::chrono::duration_cast<std::chrono::milliseconds>(end - begin);
    std::cout << "The time: " << elapsed_ms.count() << " ms\n";
    fclose(file);


    return 0;
}